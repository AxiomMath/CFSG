module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5Defs
import CFSG.GroupTheory.IrreducibleAbelianAction

public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup CFSG.Quasithin.OperatorJH CFSG.GroupTheory

variable {G : Type} [Group G] {n : ℕ}

private theorem exists_addMonoidHom_embedding {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] [Nontrivial V] (hn : n ≠ 0) {ζ : GaloisField 2 n}
    (hζ : orderOf ζ = 2 ^ n - 1) (T₁ T₂ : Module.End (ZMod 2) V) (hT : T₁ * T₂ = T₂ * T₁)
    (h₁ : T₁ ^ (2 ^ n - 1) = 1) (h₂ : T₂ ^ (2 ^ n - 1) = 1)
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ v ∈ W, T₁ v ∈ W) → (∀ v ∈ W, T₂ v ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    ∃ (x z : ℕ) (β : V →+ GaloisField 2 n), Function.Injective β ∧
      (∀ v, β (T₁ v) = ζ ^ x * β v) ∧ (∀ v, β (T₂ v) = ζ ^ z * β v) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn2 : 1 < 2 ^ n := Nat.one_lt_two_pow hn
  set N : ℕ := 2 ^ n - 1 with hNdef
  have hN : N ≠ 0 := by omega
  have hNn : N + 1 = 2 ^ n := by omega
  haveI : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := V →ₗ[ZMod 2] V))
  haveI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  let u₁ : LinearMap.GeneralLinearGroup (ZMod 2) V := (IsUnit.of_pow_eq_one h₁ hN).unit
  let u₂ : LinearMap.GeneralLinearGroup (ZMod 2) V := (IsUnit.of_pow_eq_one h₂ hN).unit
  have hu₁₂ : Commute u₁ u₂ := Units.ext hT
  let A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) := Subgroup.closure {u₁, u₂}
  have hu₁A : u₁ ∈ A := Subgroup.subset_closure (by simp)
  have hu₂A : u₂ ∈ A := Subgroup.subset_closure (by simp)
  haveI : IsMulCommutative A := Subgroup.isMulCommutative_closure (by
    intro x hx y hy hxy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hu₁₂
    · exact hu₁₂.symm
    · exact absurd rfl hxy)
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    Subgroup.mul_comm_of_mem_isMulCommutative A ha hb
  have hAN : ∀ a ∈ A, a ^ N = 1 := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact Units.ext h₁
      · exact Units.ext h₂
    | one => exact one_pow _
    | mul x y hx hy hxN hyN =>
      rw [(show Commute x y from hAcomm x hx y hy).mul_pow, hxN, hyN, one_mul]
    | inv x hx hxN => rw [inv_pow, hxN, inv_one]
  have hirrA : ∀ W : Submodule (ZMod 2) V,
      (∀ a ∈ A, ∀ v ∈ W, (a : Module.End (ZMod 2) V) v ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => hirr W (fun v hv => hW u₁ hu₁A v hv) (fun v hv => hW u₂ hu₂A v hv)
  have hKfield := adjoin_isField_of_irreducible hAcomm hirrA
  set K := Algebra.adjoin (ZMod 2) (Set.range (glEndHom A))
  letI : Field K := hKfield.toField
  haveI : Finite K := Subtype.finite
  haveI : CharP K 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  have hgen : ∀ a ∈ A, (a : Module.End (ZMod 2) V) ∈ K := fun a ha =>
    Algebra.subset_adjoin ⟨⟨a, ha⟩, by simp⟩
  let t₁ : K := ⟨(u₁ : Module.End (ZMod 2) V), hgen u₁ hu₁A⟩
  let t₂ : K := ⟨(u₂ : Module.End (ZMod 2) V), hgen u₂ hu₂A⟩
  have hfrob : ∀ y : K, y ^ 2 ^ n = y := by
    rintro ⟨y, hy⟩
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      apply Subtype.ext
      simp only [glEndHom_apply, Subalgebra.coe_pow]
      have h1 : ((a : LinearMap.GeneralLinearGroup (ZMod 2) V)) ^ 2 ^ n =
          (a : LinearMap.GeneralLinearGroup (ZMod 2) V) := by
        rw [← hNn, pow_succ, hAN a a.2, one_mul]
      have := congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod 2) V =>
        (u : Module.End (ZMod 2) V)) h1
      simpa using this
    | algebraMap c =>
      apply Subtype.ext
      simp only [Subalgebra.coe_pow]
      rw [← map_pow, ZMod.pow_card_pow]
    | add x y hx hy ihx ihy =>
      exact (add_pow_char_pow (⟨x, hx⟩ : K) ⟨y, hy⟩ 2 n).trans
        (congrArg₂ (· + ·) ihx ihy)
    | mul x y hx hy ihx ihy =>
      exact (mul_pow (⟨x, hx⟩ : K) ⟨y, hy⟩ _).trans (congrArg₂ (· * ·) ihx ihy)
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  let ev : K →+ V :=
    { toFun := fun k => (k : Module.End (ZMod 2) V) v₀
      map_zero' := by simp
      map_add' := fun a b => by simp }
  have ev_mul : ∀ a b : K, ev (a * b) = (a : Module.End (ZMod 2) V) (ev b) := fun a b => rfl
  have ev_one : ev 1 = v₀ := rfl
  have ev_inj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro k hk
    by_contra hk0
    have h1 : ev (k⁻¹ * k) = 0 := by rw [ev_mul, hk, map_zero]
    rw [inv_mul_cancel₀ hk0, ev_one] at h1
    exact hv₀ h1
  have ev_surj : Function.Surjective ev := by
    let W : Submodule (ZMod 2) V := LinearMap.range (AddMonoidHom.toZModLinearMap 2 ev)
    have hWinv : ∀ a ∈ A, ∀ v ∈ W, (a : Module.End (ZMod 2) V) v ∈ W := by
      rintro a ha v ⟨k, rfl⟩
      exact ⟨⟨a, hgen a ha⟩ * k, ev_mul _ _⟩
    rcases hirrA W hWinv with hbot | htop
    · exfalso
      have hv : v₀ ∈ W := ⟨1, ev_one⟩
      rw [hbot] at hv
      exact hv₀ (Submodule.mem_bot _ |>.mp hv)
    · intro v
      have hv : v ∈ W := by rw [htop]; trivial
      obtain ⟨k, hk⟩ := hv
      exact ⟨k, hk⟩
  have hKcard : 2 ^ Module.finrank (ZMod 2) K = Nat.card K :=
    FiniteField.pow_finrank_eq_natCard 2 K
  have hdvd : Module.finrank (ZMod 2) K ∣ n := by
    set k := Module.finrank (ZMod 2) K
    have hexp : Monoid.exponent Kˣ ∣ N := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun u => ?_
      have h1 : u ^ (N + 1) = u := Units.ext (by simpa [hNn] using hfrob u)
      calc u ^ N = u ^ N * u * u⁻¹ := by group
        _ = 1 := by rw [← pow_succ, h1]; group
    rw [IsCyclic.exponent_eq_card, Nat.card_units, ← hKcard] at hexp
    have hg := Nat.pow_sub_one_gcd_pow_sub_one 2 k n
    rw [Nat.gcd_eq_left hexp] at hg
    have h2 : 2 ^ k = 2 ^ (Nat.gcd k n) := by
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have h3 : 1 ≤ 2 ^ (Nat.gcd k n) := Nat.one_le_two_pow
      omega
    have h3 := Nat.pow_right_injective (le_refl 2) h2
    have h4 := Nat.gcd_dvd_right k n
    rwa [← h3] at h4
  obtain ⟨ψ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2) (K := K)
    (L := GaloisField 2 n) (by rw [GaloisField.finrank 2 hn]; exact hdvd)
  have hne : ∀ f : GaloisField 2 n, f ^ N = 1 → f ≠ 0 := by
    rintro f hf rfl
    rw [zero_pow hN] at hf
    exact zero_ne_one hf
  have hpow : ∀ f : GaloisField 2 n, f ^ N = 1 → ∃ x : ℕ, f = ζ ^ x := by
    intro f hf
    have hζN : ζ ^ N = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
    have hζ0 : ζ ≠ 0 := hne ζ hζN
    let u : (GaloisField 2 n)ˣ := Units.mk0 ζ hζ0
    have hu : orderOf u = N := by rw [← hζ]; exact orderOf_units.symm
    have hcardF : Nat.card (GaloisField 2 n)ˣ = N := by
      rw [Nat.card_units, GaloisField.card 2 n hn]
    have htop : Subgroup.zpowers u = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hu, hcardF])
    have hmem : Units.mk0 f (hne f hf) ∈ Subgroup.zpowers u := by rw [htop]; trivial
    obtain ⟨x, hx⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hmem)
    exact ⟨x, by simpa [u] using (congrArg Units.val hx).symm⟩
  have ht₁ : t₁ ^ N = 1 := by
    apply Subtype.ext
    simp only [Subalgebra.coe_pow, Subalgebra.coe_one]
    exact h₁
  have ht₂ : t₂ ^ N = 1 := by
    apply Subtype.ext
    simp only [Subalgebra.coe_pow, Subalgebra.coe_one]
    exact h₂
  obtain ⟨x, hx⟩ := hpow (ψ t₁) (by rw [← map_pow, ht₁, map_one])
  obtain ⟨z, hz⟩ := hpow (ψ t₂) (by rw [← map_pow, ht₂, map_one])
  let e : K ≃+ V := AddEquiv.ofBijective ev ⟨ev_inj, ev_surj⟩
  let β : V →+ GaloisField 2 n :=
    (ψ.toRingHom : K →+* GaloisField 2 n).toAddMonoidHom.comp e.symm.toAddMonoidHom
  have hβ : ∀ k : K, β (ev k) = ψ k := fun k => by
    have : e.symm (ev k) = k := e.symm_apply_apply k
    simp [β, this]
  refine ⟨x, z, β, ψ.toRingHom.injective.comp e.symm.injective, ?_, ?_⟩
  · intro v
    obtain ⟨k, rfl⟩ := ev_surj v
    have h1 : (T₁ : Module.End (ZMod 2) V) (ev k) = ev (t₁ * k) := (ev_mul t₁ k).symm
    rw [h1, hβ, hβ, map_mul, hx]
  · intro v
    obtain ⟨k, rfl⟩ := ev_surj v
    have h1 : (T₂ : Module.End (ZMod 2) V) (ev k) = ev (t₂ * k) := (ev_mul t₂ k).symm
    rw [h1, hβ, hβ, map_mul, hz]

private theorem exists_embedding_of_exp_two {Q : Type} [Group Q] [Finite Q] [Nontrivial Q]
    (hcomm : ∀ a b : Q, a * b = b * a) (hexp : ∀ a : Q, a ^ 2 = 1) (hn : n ≠ 0)
    {ζ : GaloisField 2 n} (hζ : orderOf ζ = 2 ^ n - 1) (t₁ t₂ : Monoid.End Q)
    (ht : t₁ * t₂ = t₂ * t₁) (h₁ : t₁ ^ (2 ^ n - 1) = 1) (h₂ : t₂ ^ (2 ^ n - 1) = 1)
    (hirr : ∀ P : Subgroup Q, (∀ q ∈ P, t₁ q ∈ P) → (∀ q ∈ P, t₂ q ∈ P) → P = ⊥ ∨ P = ⊤) :
    ∃ (x z : ℕ) (β : Q → GaloisField 2 n), (∀ a b, β (a * b) = β a + β b) ∧
      (∀ a, β a = 0 ↔ a = 1) ∧ (∀ a, β (t₁ a) = ζ ^ x * β a) ∧
      (∀ a, β (t₂ a) = ζ ^ z * β a) := by
  classical
  letI : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hcomm }
  letI : Module (ZMod 2) (Additive Q) := elemModule 2 hexp
  let T : Monoid.End Q →* Module.End (ZMod 2) (Additive Q) :=
    { toFun := fun f => AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive f)
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  have hT : ∀ (f : Monoid.End Q) (a : Q), T f (Additive.ofMul a) = Additive.ofMul (f a) :=
    fun _ _ => rfl
  have hirrV : ∀ W : Submodule (ZMod 2) (Additive Q), (∀ v ∈ W, T t₁ v ∈ W) →
      (∀ v ∈ W, T t₂ v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW₁ hW₂
    let P : Subgroup Q := AddSubgroup.toSubgroup' W.toAddSubgroup
    have hP : ∀ q, q ∈ P ↔ Additive.ofMul q ∈ W := fun q => AddSubgroup.mem_toSubgroup' _ _
    rcases hirr P (fun q hq => (hP _).2 (hW₁ _ ((hP _).1 hq)))
      (fun q hq => (hP _).2 (hW₂ _ ((hP _).1 hq))) with h | h
    · left
      refine (Submodule.eq_bot_iff W).2 fun v hv => ?_
      have hv' : Additive.toMul v ∈ P := (hP _).2 hv
      rw [h, Subgroup.mem_bot] at hv'
      exact (Additive.toMul.injective (by simpa using hv'))
    · right
      refine (Submodule.eq_top_iff').2 fun v => ?_
      have hv' : Additive.toMul v ∈ P := by rw [h]; trivial
      exact (hP _).1 hv'
  obtain ⟨x, z, β, hinj, hx, hz⟩ := exists_addMonoidHom_embedding hn hζ (T t₁) (T t₂)
    (by rw [← map_mul, ht, map_mul]) (by rw [← map_pow, h₁, map_one])
    (by rw [← map_pow, h₂, map_one]) hirrV
  refine ⟨x, z, fun a => β (Additive.ofMul a), fun a b => map_add β _ _, fun a => ?_,
    fun a => ?_, fun a => ?_⟩
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · simpa using (injective_iff_map_eq_zero β).1 hinj _ h
    · simp [h]
  · exact (hT t₁ a) ▸ hx _
  · exact (hT t₂ a) ▸ hz _

private abbrev repSec (C S : Subgroup G) : Type := ↥S ⧸ C.subgroupOf S

private theorem conj_mem_of_mem_inf {C S : Subgroup G}
    (l : ↥(normalizer (S : Set G) ⊓ normalizer (C : Set G))) (s : ↥S) :
    (l : G) * s * (l : G)⁻¹ ∈ S :=
  (mem_normalizer_iff.mp l.2.1 s).mp s.2

section Conj

variable {C S : Subgroup G} [(C.subgroupOf S).Normal]

private def repConj {l : G} (hS : l ∈ normalizer (S : Set G)) (hC : l ∈ normalizer (C : Set G)) :
    Monoid.End (repSec C S) :=
  QuotientGroup.map (C.subgroupOf S) (C.subgroupOf S)
    { toFun := fun s => ⟨l * s * l⁻¹, (mem_normalizer_iff.mp hS s).mp s.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [coe_mul]; group) }
    (fun c hc => by
      rw [mem_comap]
      exact mem_subgroupOf.mpr ((mem_normalizer_iff.mp hC (c : G)).mp (mem_subgroupOf.mp hc)))

private theorem repConj_mk {l : G} (hS : l ∈ normalizer (S : Set G))
    (hC : l ∈ normalizer (C : Set G)) (s s' : ↥S) (h : (s' : G) = l * s * l⁻¹) :
    repConj hS hC (QuotientGroup.mk s) = (QuotientGroup.mk s' : repSec C S) := by
  obtain rfl : s' = ⟨l * s * l⁻¹, (mem_normalizer_iff.mp hS s).mp s.2⟩ := Subtype.ext h
  rfl

private def repAct :
    ↥(normalizer (S : Set G) ⊓ normalizer (C : Set G)) →* Monoid.End (repSec C S) where
  toFun l := repConj l.2.1 l.2.2
  map_one' := by
    refine MonoidHom.ext fun q => ?_
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    exact repConj_mk _ _ s s (by simp)
  map_mul' l₁ l₂ := by
    refine MonoidHom.ext fun q => ?_
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    let s₂ : ↥S := ⟨l₂ * s * (l₂ : G)⁻¹, conj_mem_of_mem_inf l₂ s⟩
    let s₃ : ↥S := ⟨l₁ * s₂ * (l₁ : G)⁻¹, conj_mem_of_mem_inf l₁ s₂⟩
    change repConj (l₁ * l₂).2.1 (l₁ * l₂).2.2 (QuotientGroup.mk s) =
      repConj l₁.2.1 l₁.2.2 (repConj l₂.2.1 l₂.2.2 (QuotientGroup.mk s))
    rw [repConj_mk l₂.2.1 l₂.2.2 s s₂ rfl, repConj_mk l₁.2.1 l₁.2.2 s₂ s₃ rfl,
      repConj_mk (l₁ * l₂).2.1 (l₁ * l₂).2.2 s s₃ (by simp [s₃, s₂, mul_assoc])]

private theorem repAct_mk (l : ↥(normalizer (S : Set G) ⊓ normalizer (C : Set G))) (s s' : ↥S)
    (h : (s' : G) = l * s * (l : G)⁻¹) :
    repAct l (QuotientGroup.mk s) = (QuotientGroup.mk s' : repSec C S) :=
  repConj_mk l.2.1 l.2.2 s s' h

private def repPreim (P : Subgroup (repSec C S)) : Subgroup G :=
  (P.comap (QuotientGroup.mk' (C.subgroupOf S))).map S.subtype

private theorem mem_repPreim {P : Subgroup (repSec C S)} {g : G} :
    g ∈ repPreim P ↔ ∃ h : g ∈ S, (QuotientGroup.mk ⟨g, h⟩ : repSec C S) ∈ P := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.2, hs⟩
  · rintro ⟨h, hP⟩
    exact ⟨⟨g, h⟩, hP, rfl⟩

private theorem eq_bot_or_top_of_repInvariant [Finite G] {d₁ d₂ : G}
    (hY : IsYSimple (zpowers d₁ ⊔ zpowers d₂) C S) (t₁ t₂ : Monoid.End (repSec C S))
    (ht₁ : ∀ s s' : ↥S, (s' : G) = d₁ * s * d₁⁻¹ →
      t₁ (QuotientGroup.mk s) = QuotientGroup.mk s')
    (ht₂ : ∀ s s' : ↥S, (s' : G) = d₂ * s * d₂⁻¹ →
      t₂ (QuotientGroup.mk s) = QuotientGroup.mk s')
    (P : Subgroup (repSec C S)) [P.Normal] (h₁ : ∀ q ∈ P, t₁ q ∈ P) (h₂ : ∀ q ∈ P, t₂ q ∈ P) :
    P = ⊥ ∨ P = ⊤ := by
  have hd₁ : d₁ ∈ zpowers d₁ ⊔ zpowers d₂ := mem_sup_left (mem_zpowers d₁)
  have hd₂ : d₂ ∈ zpowers d₁ ⊔ zpowers d₂ := mem_sup_right (mem_zpowers d₂)
  have hnorm : ∀ (d : G) (_ : d ∈ zpowers d₁ ⊔ zpowers d₂) (t : Monoid.End (repSec C S)),
      (∀ s s' : ↥S, (s' : G) = d * s * d⁻¹ →
        t (QuotientGroup.mk s) = QuotientGroup.mk s') →
      (∀ q ∈ P, t q ∈ P) → d ∈ normalizer (repPreim P : Set G) := by
    intro d hd t ht hP
    refine mem_normalizer_of_conj_mem_of fun k hk => ?_
    obtain ⟨hkS, hkP⟩ := mem_repPreim.mp hk
    have hdk : d * k * d⁻¹ ∈ S := (mem_normalizer_iff.mp (hY.2.2.2.1 hd) k).mp hkS
    refine mem_repPreim.mpr ⟨hdk, ?_⟩
    have := hP _ hkP
    rwa [ht ⟨k, hkS⟩ ⟨d * k * d⁻¹, hdk⟩ rfl] at this
  have hYJ : zpowers d₁ ⊔ zpowers d₂ ≤ normalizer (repPreim P : Set G) :=
    sup_le (zpowers_le.mpr (hnorm d₁ hd₁ t₁ ht₁ h₁)) (zpowers_le.mpr (hnorm d₂ hd₂ t₂ ht₂ h₂))
  have hSJ : S ≤ normalizer (repPreim P : Set G) := by
    intro s hs
    refine mem_normalizer_of_conj_mem_of fun k hk => ?_
    obtain ⟨hkS, hkP⟩ := mem_repPreim.mp hk
    have hsk : s * k * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hs hkS) (S.inv_mem hs)
    refine mem_repPreim.mpr ⟨hsk, ?_⟩
    exact Normal.conj_mem ‹P.Normal› _ hkP (QuotientGroup.mk ⟨s, hs⟩)
  have hCJ : C ≤ repPreim P := by
    intro c hc
    refine mem_repPreim.mpr ⟨hY.1.le hc, ?_⟩
    have : (QuotientGroup.mk ⟨c, hY.1.le hc⟩ : repSec C S) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hc)
    rw [this]
    exact P.one_mem
  have hJS : repPreim P ≤ S := fun g hg => (mem_repPreim.mp hg).1
  rcases hY.2.2.2.2 (repPreim P) hCJ hJS hSJ hYJ with hC' | hS'
  · left
    refine eq_bot_iff.2 fun q hq => ?_
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    have hs : (s : G) ∈ repPreim P := mem_repPreim.mpr ⟨s.2, hq⟩
    rw [hC'] at hs
    have h1 : (QuotientGroup.mk s : repSec C S) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hs)
    rw [h1]
    exact one_mem _
  · right
    refine eq_top_iff.2 fun q _ => ?_
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    have hs : (s : G) ∈ repPreim P := by rw [hS']; exact s.2
    obtain ⟨h, hmem⟩ := mem_repPreim.mp hs
    exact hmem

end Conj

private def repCentralInv (Q : Type) [Group Q] : Subgroup Q where
  carrier := {q | q ∈ center Q ∧ q ^ 2 = 1}
  one_mem' := ⟨one_mem _, one_pow _⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
    rw [(show Commute a b from mem_center_iff.mp hb.1 a).mul_pow, ha.2, hb.2, one_mul]⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

private instance repCentralInv_normal (Q : Type) [Group Q] :
    (repCentralInv Q).Normal :=
  ⟨fun n hn g => by
    have h : g * n * g⁻¹ = n := by rw [mem_center_iff.mp hn.1 g, mul_inv_cancel_right]
    rw [h]
    exact hn⟩

section Elementary

variable {C S : Subgroup G} [(C.subgroupOf S).Normal]

private theorem repSec_nontrivial (hlt : C < S) : Nontrivial (repSec C S) := by
  obtain ⟨s, hsS, hsC⟩ := SetLike.exists_of_lt hlt
  refine ⟨⟨QuotientGroup.mk ⟨s, hsS⟩, 1, fun h => hsC ?_⟩⟩
  exact mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h)

private theorem center_and_sq_eq_one [Finite G] {d₁ d₂ : G}
    (hY : IsYSimple (zpowers d₁ ⊔ zpowers d₂) C S) (hS : IsPGroup 2 S)
    (t₁ t₂ : Monoid.End (repSec C S))
    (ht₁ : ∀ s s' : ↥S, (s' : G) = d₁ * s * d₁⁻¹ →
      t₁ (QuotientGroup.mk s) = QuotientGroup.mk s')
    (ht₂ : ∀ s s' : ↥S, (s' : G) = d₂ * s * d₂⁻¹ →
      t₂ (QuotientGroup.mk s) = QuotientGroup.mk s')
    (hs₁ : Function.Surjective t₁) (hs₂ : Function.Surjective t₂) :
    ∀ q : repSec C S, q ∈ center (repSec C S) ∧ q ^ 2 = 1 := by
  classical
  haveI : Nontrivial (repSec C S) := repSec_nontrivial hY.1
  have hQ : IsPGroup 2 (repSec C S) := hS.to_quotient (C.subgroupOf S)
  have hinv : ∀ t : Monoid.End (repSec C S), Function.Surjective t →
      ∀ q ∈ repCentralInv (repSec C S), t q ∈ repCentralInv (repSec C S) := by
    intro t hts q hq
    refine ⟨?_, by rw [← map_pow, hq.2, map_one]⟩
    rw [mem_center_iff]
    intro r
    obtain ⟨r', rfl⟩ := hts r
    rw [← map_mul, ← map_mul, mem_center_iff.mp hq.1 r']
  rcases eq_bot_or_top_of_repInvariant hY t₁ t₂ ht₁ ht₂ (repCentralInv (repSec C S))
    (hinv t₁ hs₁) (hinv t₂ hs₂) with hbot | htop
  · exfalso
    haveI := hQ.center_nontrivial
    have hcp : IsPGroup 2 (center (repSec C S)) :=
      hQ.of_injective (center (repSec C S)).subtype Subtype.val_injective
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hcp
    have h2 : 2 ∣ Nat.card (center (repSec C S)) := by
      have h1 : 1 < Nat.card (center (repSec C S)) := Finite.one_lt_card
      rw [hm] at h1 ⊢
      have hm0 : m ≠ 0 := by
        rintro rfl
        norm_num at h1
      exact dvd_pow_self 2 hm0
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hzP : (z : repSec C S) ∈ repCentralInv (repSec C S) := by
      refine ⟨z.2, ?_⟩
      have := pow_orderOf_eq_one z
      rw [hz] at this
      exact congrArg Subtype.val this
    rw [hbot, mem_bot] at hzP
    have : z = 1 := Subtype.ext hzP
    rw [this, orderOf_one] at hz
    norm_num at hz
  · intro q
    have hq : q ∈ repCentralInv (repSec C S) := by rw [htop]; trivial
    exact hq

end Elementary

theorem exists_isChiEmb [Finite G] {ζ : GaloisField 2 n} {d₁ d₂ : G} {C S : Subgroup G}
    (hY : IsYSimple (zpowers d₁ ⊔ zpowers d₂) C S) (hS : IsPGroup 2 S) (hcomm : Commute d₁ d₂)
    (h₁ : d₁ ^ (2 ^ n - 1) = 1) (h₂ : d₂ ^ (2 ^ n - 1) = 1) (hn : n ≠ 0)
    (hζ : orderOf ζ = 2 ^ n - 1) :
    ∃ φ β, IsChiEmb ζ d₁ d₂ C S φ β := by
  classical
  haveI : (C.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer hY.1.le).2 hY.2.1
  have hd₁ : d₁ ∈ zpowers d₁ ⊔ zpowers d₂ := mem_sup_left (mem_zpowers d₁)
  have hd₂ : d₂ ∈ zpowers d₁ ⊔ zpowers d₂ := mem_sup_right (mem_zpowers d₂)
  let a₁ : ↥(normalizer (S : Set G) ⊓ normalizer (C : Set G)) :=
    ⟨d₁, hY.2.2.2.1 hd₁, hY.2.2.1 hd₁⟩
  let a₂ : ↥(normalizer (S : Set G) ⊓ normalizer (C : Set G)) :=
    ⟨d₂, hY.2.2.2.1 hd₂, hY.2.2.1 hd₂⟩
  have ha₁₂ : a₁ * a₂ = a₂ * a₁ := Subtype.ext hcomm.eq
  have ha₁ : a₁ ^ (2 ^ n - 1) = 1 := Subtype.ext (by simpa using h₁)
  have ha₂ : a₂ ^ (2 ^ n - 1) = 1 := Subtype.ext (by simpa using h₂)
  have hsurj : ∀ a : ↥(normalizer (S : Set G) ⊓ normalizer (C : Set G)),
      Function.Surjective (repAct a : Monoid.End (repSec C S)) := by
    intro a q
    refine ⟨repAct a⁻¹ q, ?_⟩
    change (repAct a * repAct a⁻¹) q = q
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have ht₁ : ∀ s s' : ↥S, (s' : G) = d₁ * s * d₁⁻¹ →
      repAct a₁ (QuotientGroup.mk s) = (QuotientGroup.mk s' : repSec C S) :=
    fun s s' h => repAct_mk a₁ s s' h
  have ht₂ : ∀ s s' : ↥S, (s' : G) = d₂ * s * d₂⁻¹ →
      repAct a₂ (QuotientGroup.mk s) = (QuotientGroup.mk s' : repSec C S) :=
    fun s s' h => repAct_mk a₂ s s' h
  have hq := center_and_sq_eq_one hY hS (repAct a₁) (repAct a₂) ht₁ ht₂ (hsurj a₁) (hsurj a₂)
  haveI : Nontrivial (repSec C S) := repSec_nontrivial hY.1
  have hcommQ : ∀ a b : repSec C S, a * b = b * a := fun a b => (mem_center_iff.mp (hq b).1) a
  have hexpQ : ∀ a : repSec C S, a ^ 2 = 1 := fun a => (hq a).2
  have hirrQ : ∀ P : Subgroup (repSec C S), (∀ q ∈ P, repAct a₁ q ∈ P) →
      (∀ q ∈ P, repAct a₂ q ∈ P) → P = ⊥ ∨ P = ⊤ := by
    intro P hP₁ hP₂
    haveI : P.Normal := ⟨fun m hm g => by rw [hcommQ g m, mul_inv_cancel_right]; exact hm⟩
    exact eq_bot_or_top_of_repInvariant hY _ _ ht₁ ht₂ P hP₁ hP₂
  obtain ⟨x, z, β, hβm, hβ0, hβ₁, hβ₂⟩ := exists_embedding_of_exp_two hcommQ hexpQ hn hζ
    (repAct a₁) (repAct a₂) (by rw [← map_mul, ha₁₂, map_mul])
    (by rw [← map_pow, ha₁, map_one]) (by rw [← map_pow, ha₂, map_one]) hirrQ
  have hval : ∀ w : ℕ, ζ ^ ((w : ZMod (2 ^ n - 1)).val) = ζ ^ w := fun w => by
    rw [ZMod.val_natCast, ← hζ, pow_mod_orderOf]
  refine ⟨((x : ZMod (2 ^ n - 1)), (z : ZMod (2 ^ n - 1))),
    fun g => if hg : g ∈ S then β (QuotientGroup.mk ⟨g, hg⟩) else 0, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs t ht
    have hst : s * t ∈ S := S.mul_mem hs ht
    simp only [dif_pos hs, dif_pos ht, dif_pos hst]
    exact hβm (QuotientGroup.mk ⟨s, hs⟩) (QuotientGroup.mk ⟨t, ht⟩)
  · intro s hs
    simp only [dif_pos hs]
    rw [hβ0, QuotientGroup.eq_one_iff, mem_subgroupOf]
  · intro s hs
    have hs' : d₁ * s * d₁⁻¹ ∈ S := (mem_normalizer_iff.mp (hY.2.2.2.1 hd₁) s).mp hs
    simp only [dif_pos hs, dif_pos hs']
    rw [← repAct_mk a₁ ⟨s, hs⟩ ⟨d₁ * s * d₁⁻¹, hs'⟩ rfl, hβ₁, hval]
  · intro s hs
    have hs' : d₂ * s * d₂⁻¹ ∈ S := (mem_normalizer_iff.mp (hY.2.2.2.1 hd₂) s).mp hs
    simp only [dif_pos hs, dif_pos hs']
    rw [← repAct_mk a₂ ⟨s, hs⟩ ⟨d₂ * s * d₂⁻¹, hs'⟩ rfl, hβ₂, hval]

end CFSG.Quasithin.Stroth.G5

end
