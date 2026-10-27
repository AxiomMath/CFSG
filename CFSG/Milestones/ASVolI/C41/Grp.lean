module

public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Milestones.ASVolI.C41.Mod

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem burnsideC41b_le_normalizer_of_conj {X H : Subgroup G}
    (h : ∀ x ∈ X, ∀ y ∈ H, x * y * x⁻¹ ∈ H) : X ≤ Subgroup.normalizer (H : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h x hx y, fun hy => ?_⟩
  have h1 := h x⁻¹ (X.inv_mem hx) _ hy
  simpa [mul_assoc] using h1

theorem burnsideC41b_normalizer_le_normalizer_centralizer (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (H : Set G) : Set G) := by
  refine burnsideC41b_le_normalizer_of_conj fun g hg c hc => ?_
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro s hs
  have hs' : g⁻¹ * s * g ∈ H := (Subgroup.mem_normalizer_iff''.1 hg s).1 hs
  have h1 := hc _ hs'
  calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * s := by group

theorem burnsideC41b_le_normalizer_commutator {X A B : Subgroup G}
    (hA : X ≤ Subgroup.normalizer (A : Set G)) (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at *
  rw [Subgroup.map_commutator, (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hA hx),
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hB hx)]

theorem burnsideC41b_le_normalizer_of_characteristic {T C : Subgroup G} (hCT : C ≤ T)
    (hc : (C.subgroupOf T).Characteristic) : T ≤ Subgroup.normalizer (C : Set G) := by
  refine burnsideC41b_le_normalizer_of_conj fun s hs y hy => ?_
  have h1 := Subgroup.characteristic_iff_map_le.mp hc (MulAut.conj (⟨s, hs⟩ : ↥T))
  have h2 : (MulAut.conj (⟨s, hs⟩ : ↥T)) ⟨y, hCT hy⟩ ∈ C.subgroupOf T :=
    h1 ⟨⟨y, hCT hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  rw [Subgroup.mem_subgroupOf] at h2
  simpa using h2

theorem burnsideC41b_exists_pow_mem {K R : Subgroup G}
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hR : IsPGroup 2 R) {g : G} (hg : g ∈ K ⊔ R) :
    ∃ m : ℕ, g ^ (2 ^ m) ∈ K := by
  have hg' : g ∈ ((K ⊔ R : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K R hRK] at hg'
  obtain ⟨k, hk, r, hr, rfl⟩ := hg'
  obtain ⟨m, hm⟩ := hR ⟨r, hr⟩
  have hrm : r ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
  have key : ∀ j : ℕ, ∃ k' ∈ K, (k * r) ^ j = k' * r ^ j := by
    intro j
    induction j with
    | zero => exact ⟨1, K.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨k', hk', hj⟩ := ih
      refine ⟨k' * (r ^ j * k * (r ^ j)⁻¹), K.mul_mem hk' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (hRK hr) j) k).mp hk
      · rw [pow_succ, hj, pow_succ]
        group
  obtain ⟨k', hk', hj⟩ := key (2 ^ m)
  exact ⟨m, by rw [hj, hrm, mul_one]; exact hk'⟩

theorem burnsideC41b_isPGroup_of_le_sup {K R X : Subgroup G}
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hR : IsPGroup 2 R) (hX : X ≤ K ⊔ R)
    (hXK : IsPGroup 2 (X ⊓ K : Subgroup G)) : IsPGroup 2 X := by
  intro x
  obtain ⟨m, hm⟩ := burnsideC41b_exists_pow_mem hRK hR (hX x.2)
  obtain ⟨m', hm'⟩ := hXK ⟨(x : G) ^ (2 ^ m), X.pow_mem x.2 _, hm⟩
  refine ⟨m + m', Subtype.ext ?_⟩
  have h1 := congrArg Subtype.val hm'
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1 ⊢
  rw [pow_add, pow_mul]
  exact h1

theorem burnsideC41b_le_centralizer_V [Finite G] {H R M L V : Subgroup G}
    (h : HypC28 H R M L V) : ∀ r ∈ R, ∀ x ∈ V, r * x = x * r := by
  have hRO : R ≤ pCoreOf 2 (conjClosure L M ⊔ R) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right
      (sup_le (c2_9_two h).1 Subgroup.le_normalizer) h.pgroup
  intro r hr x hx
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (h.V_center hx)).2) r (hRO hr)

theorem burnsideC41b_le_normalizer_W {F : Type} [Field F] {K R W V₁ : Subgroup G}
    {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥W →* Multiplicative (Fin 3 → F)}
    (hnat : IsNaturalSectionWith K W ⊥ (CFSG.pCore 2 ↥K) (StatedSL 3 F) α β)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hRV : ∀ r ∈ R, ∀ x ∈ V₁, r * x = x * r)
    {u₀ : ↥W} (hu₀ : (u₀ : G) ∈ V₁) (hu₀1 : β u₀ ≠ 1) :
    R ≤ Subgroup.normalizer (W : Set G) := by
  obtain ⟨hKW, hαs, -, -, hβk, hβe⟩ := hnat
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have key : ∀ r ∈ R, ∀ u : ↥W, r⁻¹ * (u : G) * r ∈ W := by
    intro r hr
    let S : AddSubgroup (Fin 3 → F) :=
      { carrier := {v | ∃ u : ↥W, Multiplicative.toAdd (β u) = v ∧ r⁻¹ * (u : G) * r ∈ W}
        add_mem' := by
          rintro _ _ ⟨u₁, rfl, h₁⟩ ⟨u₂, rfl, h₂⟩
          refine ⟨u₁ * u₂, by rw [map_mul, toAdd_mul], ?_⟩
          have e : r⁻¹ * ((u₁ * u₂ : ↥W) : G) * r = (r⁻¹ * u₁ * r) * (r⁻¹ * u₂ * r) := by
            simp only [Subgroup.coe_mul]
            group
          rw [e]
          exact W.mul_mem h₁ h₂
        zero_mem' := ⟨1, by simp, by simp⟩
        neg_mem' := by
          rintro _ ⟨u, rfl, h⟩
          refine ⟨u⁻¹, by rw [map_inv, toAdd_inv], ?_⟩
          have e : r⁻¹ * ((u⁻¹ : ↥W) : G) * r = (r⁻¹ * u * r)⁻¹ := by
            simp only [InvMemClass.coe_inv]
            group
          rw [e]
          exact W.inv_mem h }
    have hS : ∀ (γ : ↥(StatedSL 3 F)) (x : Fin 3 → F), x ∈ S →
        ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x ∈ S := by
      rintro γ _ ⟨u, rfl, hu⟩
      obtain ⟨k, rfl⟩ := hαs γ
      have hku : (k : G) * u * (k : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hKW k.2) u).mp u.2
      refine ⟨⟨_, hku⟩, (hβe k u ⟨_, hku⟩ rfl), ?_⟩
      have hrk : r⁻¹ * (k : G) * r ∈ K := by
        have := (Subgroup.mem_normalizer_iff.mp (hRK (R.inv_mem hr)) k).mp k.2
        simpa using this
      have e : r⁻¹ * ((⟨_, hku⟩ : ↥W) : G) * r =
          (r⁻¹ * k * r) * (r⁻¹ * u * r) * (r⁻¹ * k * r)⁻¹ := by
        show r⁻¹ * ((k : G) * u * (k : G)⁻¹) * r = _
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hKW hrk) _).mp hu
    have hx0 : Multiplicative.toAdd (β u₀) ∈ S := by
      refine ⟨u₀, rfl, ?_⟩
      have e : r⁻¹ * (u₀ : G) * r = u₀ := by
        rw [mul_assoc, ← hRV r hr _ hu₀, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e]
      exact u₀.2
    have hne : Multiplicative.toAdd (β u₀) ≠ 0 := fun h => hu₀1 (by simpa using h)
    have htop := burnsideC41b_eq_top_of_invariant S hS hx0 hne
    intro u
    have hu : Multiplicative.toAdd (β u) ∈ S := htop ▸ AddSubgroup.mem_top _
    obtain ⟨u', hu'β, hu'W⟩ := hu
    have : u' = u := hβinj (Multiplicative.toAdd.injective hu'β)
    rw [← this]
    exact hu'W
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 := key r⁻¹ (R.inv_mem hr) ⟨x, hx⟩
    simpa using h1
  · intro hx
    have h1 := key r hr ⟨_, hx⟩
    simpa [mul_assoc] using h1

theorem burnsideC41b_inf_centralizer_le [Finite G] {F : Type} [Field F] {K R W : Subgroup G}
    {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥W →* Multiplicative (Fin 3 → F)}
    (hnat : IsNaturalSectionWith K W ⊥ (CFSG.pCore 2 ↥K) (StatedSL 3 F) α β)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hRW : R ≤ Subgroup.normalizer (W : Set G))
    (hR : IsPGroup 2 R) :
    (K ⊔ R) ⊓ Subgroup.centralizer (W : Set G) ≤ pCoreOf 2 (K ⊔ R) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKW, -, hαk, hβs, -, hβe⟩ := hnat
  have hXK : (K ⊔ R) ⊓ Subgroup.centralizer (W : Set G) ⊓ K ≤ pCoreOf 2 K := by
    rintro k ⟨⟨-, hkc⟩, hkK⟩
    have hfix : ∀ v : Fin 3 → F,
        ((α ⟨k, hkK⟩ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v = v := by
      intro v
      obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd v)
      have hku : (u : G) = k * u * k⁻¹ := by
        have hkc' : k ∈ Subgroup.centralizer (W : Set G) := hkc
        rw [Subgroup.mem_centralizer_iff] at hkc'
        rw [← hkc' u u.2, mul_inv_cancel_right]
      have h1 := hβe ⟨k, hkK⟩ u u hku
      rw [hu] at h1
      exact h1.symm
    have h1 : α ⟨k, hkK⟩ = 1 := Subtype.ext (burnsideC41b_eq_one_of_mulVec hfix)
    have h2 : (⟨k, hkK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
      rw [← hαk]
      exact h1
    exact ⟨⟨k, hkK⟩, h2, rfl⟩
  have hX2 : IsPGroup 2 ((K ⊔ R) ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) :=
    burnsideC41b_isPGroup_of_le_sup hRK hR inf_le_left
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le hXK)
  have hN : K ⊔ R ≤ Subgroup.normalizer
      (((K ⊔ R) ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer ((sup_le hKW hRW).trans
      (burnsideC41b_normalizer_le_normalizer_centralizer W))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hN hX2

theorem burnsideC41b_relIndex_sup_eq {T P : Subgroup G}
    (hTP : T ≤ Subgroup.normalizer (P : Set G)) : P.relIndex (T ⊔ P) = P.relIndex T := by
  have hPN : P ≤ Subgroup.normalizer (P : Set G) := Subgroup.le_normalizer
  haveI : (P.subgroupOf (Subgroup.normalizer (P : Set G))).Normal := Subgroup.normal_in_normalizer
  have h1 := Subgroup.relIndex_sup_right (T.subgroupOf (Subgroup.normalizer (P : Set G)))
    (P.subgroupOf (Subgroup.normalizer (P : Set G)))
  rw [← Subgroup.subgroupOf_sup hTP hPN, Subgroup.relIndex_subgroupOf (sup_le hTP hPN),
    Subgroup.relIndex_subgroupOf hTP] at h1
  exact h1

theorem burnsideC41b_le_sup_of_relIndex [Finite G] {R T P : Subgroup G} (hTR : T ≤ R)
    (hPR : P ≤ R) (hTP : T ≤ Subgroup.normalizer (P : Set G)) {b : ℕ} (hR : P.relIndex R ≤ b)
    (hT : b ≤ P.relIndex T) : R ≤ T ⊔ P := by
  have h1 := Subgroup.relIndex_mul_relIndex P (T ⊔ P) R le_sup_right (sup_le hTR hPR)
  rw [burnsideC41b_relIndex_sup_eq hTP] at h1
  have hpos : 0 < P.relIndex T :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := P.subgroupOf T))
  have hpos' : 0 < (T ⊔ P).relIndex R :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := (T ⊔ P).subgroupOf R))
  have h2 : (T ⊔ P).relIndex R ≤ 1 := by
    by_contra h
    push Not at h
    have h3 : P.relIndex T * 2 ≤ P.relIndex T * (T ⊔ P).relIndex R :=
      Nat.mul_le_mul_left _ h
    omega
  exact Subgroup.relIndex_eq_one.mp (le_antisymm h2 hpos')

theorem burnsideC41b_cocycle_mem {K Z U : Subgroup G} (hKperf : ⁅K, K⁆ = K) (hUZ : U ≤ Z)
    (hZab : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x)
    (hKU : ∀ k ∈ K, ∀ y ∈ Z, k * y * k⁻¹ * y⁻¹ ∈ U)
    (c : G → G) (hc : ∀ k ∈ K, c k ∈ Z)
    (hco : ∀ k₁ ∈ K, ∀ k₂ ∈ K, c (k₁ * k₂) = c k₁ * (k₁ * c k₂ * k₁⁻¹)) :
    ∀ k ∈ K, c k ∈ U := by
  haveI hU'n : (U.subgroupOf Z).Normal := ⟨fun n hn g => by
    have e : g * n * g⁻¹ = n := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [hZab g g.2 n n.2, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    exact hn⟩
  have hcomm : ∀ a b : ↥Z ⧸ U.subgroupOf Z, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact congrArg _ (Subtype.ext (hZab x x.2 y y.2))
  let f : ↥K →* ↥Z ⧸ U.subgroupOf Z :=
    MonoidHom.mk' (fun k => QuotientGroup.mk (⟨c k, hc k k.2⟩ : ↥Z)) fun k₁ k₂ => by
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hk₂ : (c k₂)⁻¹ ∈ Z := Z.inv_mem (hc k₂ k₂.2)
      have h1 := hKU k₁ k₁.2 _ hk₂
      have e : ((⟨c ((k₁ * k₂ : ↥K) : G), hc _ (k₁ * k₂).2⟩ : ↥Z)⁻¹ *
          (⟨c k₁, hc k₁ k₁.2⟩ * ⟨c k₂, hc k₂ k₂.2⟩) : ↥Z) =
          (k₁ : G) * (c k₂)⁻¹ * (k₁ : G)⁻¹ * ((c k₂)⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
        rw [hco k₁ k₁.2 k₂ k₂.2]
        group
      rw [e]
      exact h1
  have hf : ∀ k₁ k₂ : ↥K, f ⁅k₁, k₂⁆ = 1 := by
    intro k₁ k₂
    rw [map_commutatorElement, commutatorElement_def, hcomm (f k₁) (f k₂), mul_inv_cancel_right,
      mul_inv_cancel]
  have hle : ⁅K, K⁆ ≤ f.ker.map K.subtype := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    exact ⟨⁅(⟨g₁, h₁⟩ : ↥K), ⟨g₂, h₂⟩⁆, hf _ _, rfl⟩
  intro k hk
  rw [← hKperf] at hk
  obtain ⟨k', hk', rfl⟩ := hle hk
  have h1 : (QuotientGroup.mk (⟨c k', hc k' k'.2⟩ : ↥Z) : ↥Z ⧸ U.subgroupOf Z) = 1 := hk'
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem burnsideC41b_le_of_natural {F : Type} [Field F] {K U W : Subgroup G}
    {α : ↥K →* ↥(StatedSL 3 F)} (hα : Function.Surjective α)
    (hU : IsSumOfNaturalModulesVia K U ⊥ α false 1) (hWU : W ≤ U)
    (hKW : K ≤ Subgroup.normalizer (W : Set G)) (hW : W ≠ ⊥) : U ≤ W := by
  obtain ⟨hKU, -, β, -, hβk, hβe⟩ := hU
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have hfun : ∀ a b : Fin 1 → Fin 3 → F, a 0 = b 0 → a = b := fun a b h => by
    funext i
    rw [Subsingleton.elim i 0]
    exact h
  let S : AddSubgroup (Fin 3 → F) :=
    { carrier := {v | ∃ u : ↥U, Multiplicative.toAdd (β u) 0 = v ∧ (u : G) ∈ W}
      add_mem' := by
        rintro _ _ ⟨u₁, rfl, h₁⟩ ⟨u₂, rfl, h₂⟩
        exact ⟨u₁ * u₂, by rw [map_mul, toAdd_mul, Pi.add_apply], W.mul_mem h₁ h₂⟩
      zero_mem' := ⟨1, by simp, W.one_mem⟩
      neg_mem' := by
        rintro _ ⟨u, rfl, h⟩
        exact ⟨u⁻¹, by rw [map_inv, toAdd_inv, Pi.neg_apply], W.inv_mem h⟩ }
  have hS : ∀ (γ : ↥(StatedSL 3 F)) (x : Fin 3 → F), x ∈ S →
      ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x ∈ S := by
    rintro γ _ ⟨u, rfl, hu⟩
    obtain ⟨k, rfl⟩ := hα γ
    have hkuU : (k : G) * u * (k : G)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hKU k.2) u).mp u.2
    refine ⟨⟨_, hkuU⟩, ?_, (Subgroup.mem_normalizer_iff.mp (hKW k.2) u).mp hu⟩
    rw [hβe k u ⟨_, hkuU⟩ rfl 0]
    rfl
  obtain ⟨w, hwW, hw1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra h
    push Not at h
    exact hW (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (h x hx))
  have hwU : w ∈ U := hWU hwW
  have hx0 : Multiplicative.toAdd (β ⟨w, hwU⟩) 0 ∈ S := ⟨⟨w, hwU⟩, rfl, hwW⟩
  have hne : Multiplicative.toAdd (β ⟨w, hwU⟩) 0 ≠ 0 := by
    intro h0
    have h1 : Multiplicative.toAdd (β ⟨w, hwU⟩) = Multiplicative.toAdd (β 1) :=
      hfun _ _ (by rw [h0, map_one, toAdd_one, Pi.zero_apply])
    have h2 : (⟨w, hwU⟩ : ↥U) = 1 := hβinj (Multiplicative.toAdd.injective h1)
    exact hw1 (congrArg Subtype.val h2)
  have htop := burnsideC41b_eq_top_of_invariant S hS hx0 hne
  intro u hu
  have hmem : Multiplicative.toAdd (β ⟨u, hu⟩) 0 ∈ S := htop ▸ AddSubgroup.mem_top _
  obtain ⟨u', hu'β, hu'W⟩ := hmem
  have h1 : u' = ⟨u, hu⟩ := hβinj (Multiplicative.toAdd.injective (hfun _ _ hu'β))
  rw [h1] at hu'W
  exact hu'W

theorem burnsideC41b_conj_commutator_eq {z x k u y : G}
    (hkz : k * z * k⁻¹ = u * z) (hkx : k * x * k⁻¹ = y * x)
    (huz : Commute u z) (huy : Commute u y) (hux : Commute u x) (hzy : Commute z y)
    (hcy : Commute ⁅z, x⁆ y) : k * ⁅z, x⁆ * k⁻¹ = ⁅z, x⁆ := by
  have h1 : k * ⁅z, x⁆ * k⁻¹ = ⁅k * z * k⁻¹, k * x * k⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  rw [h1, hkz, hkx, commutatorElement_def]
  have hw : Commute u (z * y * x * z⁻¹) :=
    ((huz.mul_right huy).mul_right hux).mul_right huz.inv_right
  calc u * z * (y * x) * (u * z)⁻¹ * (y * x)⁻¹
      = u * (z * y * x * z⁻¹) * u⁻¹ * (x⁻¹ * y⁻¹) := by group
    _ = z * y * x * z⁻¹ * (x⁻¹ * y⁻¹) := by rw [hw.eq, mul_inv_cancel_right]
    _ = y * ⁅z, x⁆ * y⁻¹ := by
      rw [commutatorElement_def, hzy.eq]
      group
    _ = ⁅z, x⁆ := by rw [← hcy.eq, mul_inv_cancel_right]

theorem burnsideC41b_characteristic_commutator_center {R T : Subgroup G} (hTR : T ≤ R)
    (hT : (T.subgroupOf R).Characteristic) :
    ((⁅centerOf T, R⁆ : Subgroup G).subgroupOf R).Characteristic := by
  have hZR : centerOf T ≤ R := inf_le_left.trans hTR
  have hTmap := Subgroup.characteristic_iff_map_le.mp hT
  have hZc : ((centerOf T).subgroupOf R).Characteristic := by
    rw [Subgroup.characteristic_iff_map_le]
    intro φ
    rintro _ ⟨z, hz, rfl⟩
    have hz' : ((z : ↥R) : G) ∈ centerOf T := Subgroup.mem_subgroupOf.mp hz
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.mp hz'
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mp (hTmap φ ⟨z, Subgroup.mem_subgroupOf.mpr hzT, rfl⟩)
    · rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have hs := hTmap φ.symm ⟨⟨t, hTR ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
      rw [Subgroup.mem_subgroupOf] at hs
      have hcomm : φ.symm ⟨t, hTR ht⟩ * z = z * φ.symm ⟨t, hTR ht⟩ :=
        Subtype.ext ((Subgroup.mem_centralizer_iff.mp hzC) _ hs)
      have h2 := congrArg φ hcomm
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
      exact congrArg Subtype.val h2
  have heq : (⁅centerOf T, R⁆ : Subgroup G).subgroupOf R =
      ⁅(centerOf T).subgroupOf R, ⊤⁆ := by
    apply Subgroup.map_injective (Subgroup.subtype_injective R)
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype, inf_of_le_left hZR,
      inf_of_le_left (Subgroup.commutator_le_of_le hZR le_rfl)]
  rw [heq]
  haveI := hZc
  exact Subgroup.commutator_characteristic _ _

end CFSG.ASVolI
