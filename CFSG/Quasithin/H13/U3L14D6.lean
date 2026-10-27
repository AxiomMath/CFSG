module

public import CFSG.Quasithin.H13.U3L14D1
public import CFSG.Quasithin.EmptyFaithful.S14612EC
public import CFSG.Quasithin.Vol2.Ch1Xi
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem elemAb_comm {V : Subgroup G} (hV : IsElemAbelian 2 V) {a b : G} (ha : a ∈ V)
    (hb : b ∈ V) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hV ha hb

omit [Finite G] in
theorem elemAb_of_le {A B : Subgroup G} (hB : IsElemAbelian 2 B) (h : A ≤ B) :
    IsElemAbelian 2 A := CFSG.Open.IsElemAbelian.mono hB h

omit [Finite G] in
theorem mem_normalizer_centralizer_of {W : Subgroup G} {g : G}
    (hg : g ∈ normalizer (W : Set G)) :
    g ∈ normalizer (centralizer (W : Set G) : Set G) := by
  have key : ∀ {h : G}, h ∈ normalizer (W : Set G) → ∀ c ∈ centralizer (W : Set G),
      h * c * h⁻¹ ∈ centralizer (W : Set G) := by
    intro h hh c hc
    rw [mem_centralizer_iff] at hc ⊢
    intro w hw
    have hw' : h⁻¹ * w * h ∈ W := by
      have := (mem_normalizer_iff.1 (inv_mem hh) w).1 hw
      simpa using this
    have hcw := hc _ hw'
    calc w * (h * c * h⁻¹) = h * ((h⁻¹ * w * h) * c) * h⁻¹ := by group
      _ = h * (c * (h⁻¹ * w * h)) * h⁻¹ := by rw [hcw]
      _ = h * c * h⁻¹ * w := by group
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key hg c, fun hc => ?_⟩
  have h1 := key (inv_mem hg) _ hc
  have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
  rwa [e] at h1

omit [Finite G] in
theorem le_normalizer_commutator_of {A H K : Subgroup G} (hH : A ≤ normalizer (H : Set G))
    (hK : A ≤ normalizer (K : Set G)) : A ≤ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  have key : ∀ a ∈ A, ∀ x ∈ ⁅H, K⁆, a * x * a⁻¹ ∈ ⁅H, K⁆ := by
    intro a ha x hx
    have hle : ⁅H, K⁆ ≤ ⁅H, K⁆.comap (MulAut.conj a).toMonoidHom := by
      rw [commutator_le]
      intro h hh k hk
      have e : a * ⁅h, k⁆ * a⁻¹ = ⁅a * h * a⁻¹, a * k * a⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      show a * ⁅h, k⁆ * a⁻¹ ∈ ⁅H, K⁆
      rw [e]
      exact commutator_mem_commutator ((mem_normalizer_iff.1 (hH ha) h).1 hh)
        ((mem_normalizer_iff.1 (hK ha) k).1 hk)
    exact hle hx
  intro a ha
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key a ha x, fun hx => ?_⟩
  have h1 := key a⁻¹ (inv_mem ha) _ hx
  have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
  rwa [e] at h1

omit [Finite G] in
theorem commutator_le_left_of {V P : Subgroup G} (hN : P ≤ normalizer (V : Set G)) :
    ⁅V, P⁆ ≤ V := by
  rw [commutator_le]
  intro v hv y hy
  have h1 : y * v⁻¹ * y⁻¹ ∈ V := (mem_normalizer_iff.1 (hN hy) _).1 (inv_mem hv)
  have e : ⁅v, y⁆ = v * (y * v⁻¹ * y⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem hv h1

omit [Finite G] in
theorem exists_mul_of_mem_sup {P T : Subgroup G} (hT : T ≤ normalizer (P : Set G)) {g : G}
    (hg : g ∈ P ⊔ T) : ∃ y ∈ P, ∃ t ∈ T, g = y * t := by
  let S : Subgroup G :=
    { carrier := {g | ∃ a ∈ P, ∃ t ∈ T, g = a * t}
      one_mem' := ⟨1, P.one_mem, 1, T.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, t, ht, rfl⟩ ⟨a', ha', t', ht', rfl⟩
        have h1 : t * a' * t⁻¹ ∈ P := (mem_normalizer_iff.mp (hT ht) a').mp ha'
        refine ⟨a * (t * a' * t⁻¹), P.mul_mem ha h1, t * t', T.mul_mem ht ht', ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨a, ha, t, ht, rfl⟩
        have h1 : t⁻¹ * a⁻¹ * t ∈ P := by
          have := (mem_normalizer_iff.mp (hT (T.inv_mem ht)) a⁻¹).mp (P.inv_mem ha)
          simpa using this
        refine ⟨t⁻¹ * a⁻¹ * t, h1, t⁻¹, T.inv_mem ht, ?_⟩
        group }
  exact (sup_le (fun a ha => ⟨a, ha, 1, T.one_mem, by simp⟩)
    (fun t ht => ⟨1, P.one_mem, t, ht, by simp⟩) : P ⊔ T ≤ S) hg

theorem pCoreOf_le_centralizer_of_reduced {H W : Subgroup G} (hW : IsTwoReducedIn H W) :
    pCoreOf 2 H ≤ centralizer (W : Set G) :=
  hW.2.2.2 _ (LieType.BorelTits.pCoreOf_le 2 H) (LieType.BorelTits.le_normalizer_pCoreOf 2 H)
    fun d hd => by
      obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨d, hd⟩
      have h1 : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      exact ⟨k, by rw [h1]; exact one_mem _⟩

theorem pCoreOf_le_pCoreOf_sup_of_le {T P : Subgroup G} (hTP : T ≤ normalizer (P : Set G)) :
    pCoreOf 2 P ≤ pCoreOf 2 (P ⊔ T) :=
  LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((LieType.BorelTits.pCoreOf_le 2 P).trans le_sup_left)
    (sup_le (LieType.BorelTits.le_normalizer_pCoreOf 2 P)
      (hTP.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P)))
    (LieType.BorelTits.pCoreOf_isPGroup 2 P)

@[expose] noncomputable def actW {H W : Subgroup G} (hN : H ≤ normalizer (W : Set G)) :
    ↥H →* MulAut ↥W :=
  (CFSG.Quasithin.conjAct W).comp (inclusion hN)

omit [Finite G] in
theorem actW_apply_coe {H W : Subgroup G} (hN : H ≤ normalizer (W : Set G)) (h : ↥H)
    (w : ↥W) : ((actW hN h w : ↥W) : G) = h * w * (h : G)⁻¹ :=
  normalizerMonoidHom_apply_apply_coe W (inclusion le_rfl (inclusion hN h)) w

omit [Finite G] in
theorem actW_eq_one_iff {H W : Subgroup G} (hN : H ≤ normalizer (W : Set G)) (h : ↥H) :
    actW hN h = 1 ↔ (h : G) ∈ centralizer (W : Set G) := by
  constructor
  · intro h1
    rw [mem_centralizer_iff]
    intro w hw
    have h2 := congrArg (fun φ : MulAut ↥W => ((φ ⟨w, hw⟩ : ↥W) : G)) h1
    simp only [actW_apply_coe, MulAut.one_apply] at h2
    calc w * (h : G) = ((h : G) * w * (h : G)⁻¹) * h := by rw [h2]
      _ = h * w := by group
  · intro hc
    refine MulEquiv.ext fun w => Subtype.ext ?_
    rw [actW_apply_coe, MulAut.one_apply, ← mem_centralizer_iff.1 hc (w : G) w.2]
    group

omit [Finite G] in
theorem range_actW {H W : Subgroup G} (hN : H ≤ normalizer (W : Set G)) :
    (actW hN).range = autOn H W := by
  rw [actW, MonoidHom.range_comp, inclusion_range]
  rfl

theorem inf_centralizer_le_of_isXi {T P W : Subgroup G} (hP : IsXi T P)
    (hab : ⁅P, P⁆ ≤ pCoreOf 2 P) (hTW : T ≤ normalizer (W : Set G))
    (hPW : P ≤ normalizer (W : Set G)) (hne : ¬ P ≤ centralizer (W : Set G)) :
    P ⊓ centralizer (W : Set G) ≤ pCoreOf 2 P := by
  obtain ⟨hPu, hTP, -, p, -, -, -, -, hirr⟩ := hP
  have hTY : T ≤ normalizer
      (((P ⊓ centralizer (W : Set G)) ⊔ pCoreOf 2 P : Subgroup G) : Set G) := by
    intro t ht
    refine inf_normalizer_le_normalizer_sup _ _ ⟨inf_normalizer_le_normalizer_inf
      ⟨hTP ht, mem_normalizer_centralizer_of (hTW ht)⟩, ?_⟩
    exact LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P (hTP ht)
  rcases hirr ((P ⊓ centralizer (W : Set G)) ⊔ pCoreOf 2 P)
      (sup_le (hab.trans le_sup_right) le_sup_right)
      (sup_le inf_le_left (LieType.BorelTits.pCoreOf_le 2 P)) hTY with h | h
  · intro y hy
    have hy' : y ∈ (P ⊓ centralizer (W : Set G)) ⊔ pCoreOf 2 P := mem_sup_left hy
    rw [h] at hy'
    exact (sup_le hab le_rfl) hy'
  · exfalso
    apply hne
    have h2 : ∀ y ∈ P, ∃ k : ℕ, y ^ 2 ^ k ∈ P ⊓ centralizer (W : Set G) :=
      B6.isTwoQuotient_of_sup_eq (C := P ⊓ centralizer (W : Set G)) (D := P)
        (LieType.BorelTits.pCoreOf_isPGroup 2 P)
        (fun y hy => inf_normalizer_le_normalizer_inf
          ⟨le_normalizer hy, mem_normalizer_centralizer_of (hPW hy)⟩)
        (by rw [sup_comm]; exact h)
    calc P = oTwoUpper P := hPu
      _ ≤ P ⊓ centralizer (W : Set G) := oTwoUpper_le_of_pow_mem h2
      _ ≤ centralizer (W : Set G) := inf_le_right

theorem isPGroup_inf_centralizer {T P W : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTP : T ≤ normalizer (P : Set G)) (hC : P ⊓ centralizer (W : Set G) ≤ pCoreOf 2 P) :
    IsPGroup 2 ↥((P ⊔ T) ⊓ centralizer (W : Set G)) := by
  have h1 : ∀ d ∈ P ⊔ T, ∃ k : ℕ, d ^ 2 ^ k ∈ P :=
    B6.isTwoQuotient_of_sup_eq (C := P) (D := P ⊔ T) hT2 (sup_le le_normalizer hTP)
      (sup_comm T P)
  rintro ⟨k, hkPT, hkC⟩
  obtain ⟨m, hm⟩ := h1 k hkPT
  have h2 : k ^ 2 ^ m ∈ pCoreOf 2 P := hC ⟨hm, pow_mem hkC _⟩
  obtain ⟨n, hn⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 P ⟨_, h2⟩
  have h3 : (k ^ 2 ^ m) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  refine ⟨m + n, Subtype.ext ?_⟩
  rw [SubgroupClass.coe_pow, pow_add, pow_mul]
  exact h3

theorem pCoreOf_sup_eq_inf_centralizer {T P W : Subgroup G} (hT : IsSylowTwoOf T (P ⊔ T))
    (hTP : T ≤ normalizer (P : Set G)) (hW : IsTwoReducedIn (P ⊔ T) W)
    (hC : P ⊓ centralizer (W : Set G) ≤ pCoreOf 2 P) :
    pCoreOf 2 (P ⊔ T) = T ⊓ centralizer (W : Set G) := by
  apply le_antisymm
  · exact le_inf (pCoreOf_two_le_of_isSylowTwoOf hT) (pCoreOf_le_centralizer_of_reduced hW)
  · have hK := isPGroup_inf_centralizer hT.2.1 hTP hC
    refine le_trans (inf_le_inf_right _ le_sup_right)
      (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ hK)
    intro g hg
    exact inf_normalizer_le_normalizer_inf
      ⟨le_normalizer hg, mem_normalizer_centralizer_of (hW.2.1 hg)⟩

theorem commutator_inf_centralizer_eq_bot_of {P V : Subgroup G}
    (hN : P ≤ normalizer (V : Set G)) (hV : IsElemAbelian 2 V)
    (h3 : ∀ y ∈ P, y ^ 3 ∈ centralizer (V : Set G)) :
    ⁅V, P⁆ ⊓ centralizer (P : Set G) = ⊥ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have hsq : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV.2 v v.2)
  have h3' : ∀ y : ↥P, actW hN y ^ 3 = 1 := by
    intro y
    rw [← map_pow, actW_eq_one_iff]
    simpa using h3 y y.2
  have hodd : Odd (Nat.card (actW hN).range) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hp : IsPGroup 3 (actW hN).range := by
      rintro ⟨_, y, rfl⟩
      exact ⟨1, Subtype.ext (by simpa using h3' y)⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).mp hp
    rw [hn]
    exact Odd.pow (by decide)
  have hbot := commV_inf_fixV_eq_bot hsq hodd
  have hle : ⁅V, P⁆ ≤ (commV (actW hN).range).map V.subtype := by
    rw [commutator_le]
    intro v hv y hy
    refine ⟨actW hN ⟨y, hy⟩ ⟨v⁻¹, inv_mem hv⟩ * (⟨v⁻¹, inv_mem hv⟩ : ↥V)⁻¹,
      subset_closure ⟨actW hN ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, ⟨v⁻¹, inv_mem hv⟩, rfl⟩, ?_⟩
    have hm : y * v⁻¹ * y⁻¹ ∈ V := (mem_normalizer_iff.1 (hN hy) _).1 (inv_mem hv)
    have hc : y * v⁻¹ * y⁻¹ * v = v * (y * v⁻¹ * y⁻¹) := elemAb_comm hV hm hv
    have e1 : ((actW hN ⟨y, hy⟩ ⟨v⁻¹, inv_mem hv⟩ * (⟨v⁻¹, inv_mem hv⟩ : ↥V)⁻¹ : ↥V) : G) =
        y * v⁻¹ * y⁻¹ * v := by
      rw [Subgroup.coe_mul, actW_apply_coe, Subgroup.coe_inv]
      simp
    rw [Subgroup.coe_subtype, e1, hc, commutatorElement_def]
    group
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgc, hgC⟩ := mem_inf.1 hg
  obtain ⟨w, hw, rfl⟩ := hle hgc
  rw [Subgroup.coe_subtype] at hgC
  have hwfix : w ∈ fixV (actW hN).range := by
    rintro _ ⟨y, rfl⟩
    apply Subtype.ext
    rw [actW_apply_coe, mem_centralizer_iff.1 hgC (y : G) y.2]
    group
  have hw1 : w ∈ commV (actW hN).range ⊓ fixV (actW hN).range := ⟨hw, hwfix⟩
  rw [hbot, mem_bot] at hw1
  rw [hw1, map_one]
  exact one_mem _

@[expose] def wOf (T P V : Subgroup G) : Subgroup G :=
  conjClosure (⁅V, P⁆ ⊓ (T ⊓ centralizer (T : Set G))) (P ⊔ T)

omit [Finite G] in
theorem le_normalizer_wOf (T P V : Subgroup G) : P ⊔ T ≤ normalizer (wOf T P V : Set G) :=
  le_normalizer_conjClosure _ _

omit [Finite G] in
theorem le_wOf (T P V : Subgroup G) :
    ⁅V, P⁆ ⊓ (T ⊓ centralizer (T : Set G)) ≤ wOf T P V :=
  le_conjClosure _ _

omit [Finite G] in
theorem wOf_le_commutator {T P V : Subgroup G} (hTP : T ≤ normalizer (P : Set G))
    (hTV : P ⊔ T ≤ normalizer (V : Set G)) : wOf T P V ≤ ⁅V, P⁆ := by
  have hcomm : P ⊔ T ≤ normalizer ((⁅V, P⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of hTV (sup_le le_normalizer hTP)
  exact conjClosure_le fun h hh z hz => (mem_normalizer_iff.1 (hcomm hh) z).1 (mem_inf.1 hz).1

omit [Finite G] in
theorem wOf_le {T P V : Subgroup G} (hTP : T ≤ normalizer (P : Set G))
    (hTV : P ⊔ T ≤ normalizer (V : Set G)) : wOf T P V ≤ V :=
  (wOf_le_commutator hTP hTV).trans (commutator_le_left_of (le_sup_left.trans hTV))

theorem wOf_ne_bot {T P V : Subgroup G} (hT2 : IsPGroup 2 T) (hTP : T ≤ normalizer (P : Set G))
    (hTV : P ⊔ T ≤ normalizer (V : Set G)) (hVT : V ≤ T) (hne : ⁅V, P⁆ ≠ ⊥) :
    wOf T P V ≠ ⊥ := by
  have hTc : T ≤ normalizer ((⁅V, P⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of (le_sup_right.trans hTV) hTP
  have hcT : ⁅V, P⁆ ≤ T := (commutator_le_left_of (le_sup_left.trans hTV)).trans hVT
  have hZ : ⁅V, P⁆ ⊓ (T ⊓ centralizer (T : Set G)) ≠ ⊥ := by
    have : Group.IsNilpotent T := hT2.isNilpotent
    have hnormal : (⁅V, P⁆.subgroupOf T).Normal :=
      normal_subgroupOf_of_le_normalizer hTc
    have hne' : ⁅V, P⁆.subgroupOf T ≠ ⊥ := by
      intro h
      apply hne
      rw [← map_subgroupOf_eq_of_le hcT, h, Subgroup.map_bot]
    obtain ⟨⟨y, hy⟩, hy1⟩ := ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
    have hyC : (y : G) ∈ centralizer (T : Set G) := by
      rw [mem_centralizer_iff]
      intro t ht
      exact congrArg Subtype.val (mem_center_iff.mp hy.2 ⟨t, ht⟩)
    intro h
    have hmem : (y : G) ∈ ⁅V, P⁆ ⊓ (T ⊓ centralizer (T : Set G)) := ⟨hy.1, y.2, hyC⟩
    rw [h, mem_bot] at hmem
    exact hy1 (Subtype.ext (Subtype.ext hmem))
  intro h
  apply hZ
  rw [eq_bot_iff]
  exact (le_wOf T P V).trans h.le

theorem wOf_inf_centralizer {T P V : Subgroup G} (hTP : T ≤ normalizer (P : Set G))
    (hTV : P ⊔ T ≤ normalizer (V : Set G)) (hV : IsElemAbelian 2 V)
    (h3 : ∀ y ∈ P, y ^ 3 ∈ centralizer (V : Set G)) :
    wOf T P V ⊓ centralizer (P : Set G) = ⊥ := by
  rw [eq_bot_iff, ← commutator_inf_centralizer_eq_bot_of (le_sup_left.trans hTV) hV h3]
  exact inf_le_inf_right _ (wOf_le_commutator hTP hTV)

omit [Finite G] in
theorem isTwoReducedIn_wOf {T P V : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTP : T ≤ normalizer (P : Set G)) (hV : IsTwoReducedIn (P ⊔ T) V)
    (h3 : ∀ y ∈ P, y ^ 3 ∈ centralizer (V : Set G)) :
    IsTwoReducedIn (P ⊔ T) (wOf T P V) := by
  have hWV : wOf T P V ≤ V := wOf_le hTP hV.2.1
  have hN := le_normalizer_wOf T P V
  have hCW : centralizer (V : Set G) ≤ centralizer (wOf T P V : Set G) := centralizer_le hWV
  refine ⟨hWV.trans hV.1, hN, elemAb_of_le hV.2.2.1 hWV, fun D hD hDN hD2 => ?_⟩
  have hDb : IsPGroup 2 ((D.subgroupOf (P ⊔ T)).map (actW hN)) := by
    rintro ⟨_, d, hd, rfl⟩
    obtain ⟨k, hk⟩ := hD2 d (mem_subgroupOf.1 hd)
    refine ⟨k, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, ← map_pow, OneMemClass.coe_one, actW_eq_one_iff]
    simpa using hk
  have hTb : IsPGroup 2 ((T.subgroupOf (P ⊔ T)).map (actW hN)) := by
    rintro ⟨_, t, ht, rfl⟩
    obtain ⟨k, hk⟩ := hT2 ⟨t, mem_subgroupOf.1 ht⟩
    have h1 : t ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    refine ⟨k, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, ← map_pow, h1, map_one, OneMemClass.coe_one]
  have hTbN : (T.subgroupOf (P ⊔ T)).map (actW hN) ≤
      normalizer ((D.subgroupOf (P ⊔ T)).map (actW hN) : Set (MulAut ↥(wOf T P V))) := by
    rintro _ ⟨t, -, rfl⟩
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨d, hd, rfl⟩
      refine ⟨t * d * t⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      simp only [SetLike.mem_coe, mem_subgroupOf] at hd ⊢
      simpa using (mem_normalizer_iff.1 (hDN t.2) d).1 hd
    · rintro ⟨d, hd, hdx⟩
      refine ⟨t⁻¹ * d * t, ?_, ?_⟩
      · simp only [SetLike.mem_coe, mem_subgroupOf] at hd ⊢
        have := (mem_normalizer_iff.1 (hDN (inv_mem t.2)) d).1 hd
        simpa using this
      · rw [map_mul, map_mul, map_inv, hdx]
        group
  have hDT := hTb.to_sup_of_normal_right' hDb hTbN
  have key : ∀ d ∈ D, ∃ t ∈ T, ∀ w ∈ wOf T P V, d * w * d⁻¹ = t * w * t⁻¹ := by
    intro d hd
    obtain ⟨y, hy, t, ht, rfl⟩ := exists_mul_of_mem_sup hTP (hD hd)
    refine ⟨t, ht, fun w hw => ?_⟩
    have hdd : (⟨y * t, hD hd⟩ : ↥(P ⊔ T)) =
        (⟨y, mem_sup_left hy⟩ : ↥(P ⊔ T)) * ⟨t, mem_sup_right ht⟩ := rfl
    have hmem : actW hN ⟨y, mem_sup_left hy⟩ ∈ (T.subgroupOf (P ⊔ T)).map (actW hN) ⊔
        (D.subgroupOf (P ⊔ T)).map (actW hN) := by
      have e : actW hN ⟨y, mem_sup_left hy⟩ =
          (actW hN ⟨t, mem_sup_right ht⟩ * (actW hN ⟨y * t, hD hd⟩)⁻¹)⁻¹ := by
        rw [hdd, map_mul]
        group
      rw [e]
      exact inv_mem (mul_mem (mem_sup_left ⟨_, mem_subgroupOf.2 ht, rfl⟩)
        (inv_mem (mem_sup_right ⟨_, mem_subgroupOf.2 hd, rfl⟩)))
    obtain ⟨k, hk⟩ := hDT ⟨_, hmem⟩
    have hk' : actW hN ⟨y, mem_sup_left hy⟩ ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have h3' : actW hN ⟨y, mem_sup_left hy⟩ ^ 3 = 1 := by
      rw [← map_pow, actW_eq_one_iff]
      exact hCW (by simpa using h3 y hy)
    have hy1 : actW hN ⟨y, mem_sup_left hy⟩ = 1 :=
      eq_one_of_pow_two_pow_of_odd (by decide) hk' h3'
    have hdt : actW hN ⟨y * t, hD hd⟩ = actW hN ⟨t, mem_sup_right ht⟩ := by
      rw [hdd, map_mul, hy1, one_mul]
    have h4 := congrArg (fun φ : MulAut ↥(wOf T P V) => ((φ ⟨w, hw⟩ : ↥(wOf T P V)) : G)) hdt
    simpa only [actW_apply_coe] using h4
  have hC0 : ∀ d ∈ D, ∀ c ∈ ⁅V, P⁆ ⊓ (T ⊓ centralizer (T : Set G)), d * c * d⁻¹ = c := by
    intro d hd c hc
    obtain ⟨t, ht, hdt⟩ := key d hd
    rw [hdt c (le_wOf T P V hc)]
    have htc : t * c = c * t := mem_centralizer_iff.1 (mem_inf.1 (mem_inf.1 hc).2).2 t ht
    rw [htc]
    group
  rw [le_centralizer_iff]
  refine conjClosure_le fun g hg c hc => ?_
  rw [mem_centralizer_iff]
  intro d hd
  have hd' : g⁻¹ * d * g ∈ D := by
    have := (mem_normalizer_iff.1 (hDN (inv_mem hg)) d).1 hd
    simpa using this
  have h5 := hC0 _ hd' c hc
  calc d * (g * c * g⁻¹) = g * ((g⁻¹ * d * g) * c * (g⁻¹ * d * g)⁻¹) * g⁻¹ * d := by group
    _ = g * c * g⁻¹ * d := by rw [h5]

end CFSG.Quasithin.H13.U3
