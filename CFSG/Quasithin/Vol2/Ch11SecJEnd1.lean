module

public import CFSG.Quasithin.Vol2.Ch11SecJFacts
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecJ

open scoped MatrixGroups Matrix

structure NatPair {G : Type} [Group G] (U V V₁ W K : Subgroup G) {F : Type} [Field F]
    (α : ↥K →* SL(2, F)) (βV : ↥V →* Multiplicative (Fin 2 → F))
    (βU : ↥U →* Multiplicative (Fin 2 → F)) : Prop where
  hV₁V : V₁ ≤ V
  hVU : V ≤ U
  hV₁W : V₁ ≤ W
  hWU : W ≤ U
  hWV : W ⊓ V = V₁
  hWVU : W ⊔ V = U
  hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ V₁
  hKV : K ≤ Subgroup.normalizer (V : Set G)
  hKW : K ≤ Subgroup.normalizer (W : Set G)
  hβV : Function.Surjective βV
  hkerV : βV.ker = V₁.subgroupOf V
  hβU : Function.Surjective βU
  hkerU : βU.ker = V.subgroupOf U
  eqV : ∀ (k : ↥K) (a b : ↥V), (b : G) = k * a * k⁻¹ →
    Multiplicative.toAdd (βV b) =
      ((α k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (βV a)
  eqU : ∀ (k : ↥K) (a b : ↥U), (b : G) = k * a * k⁻¹ →
    Multiplicative.toAdd (βU b) =
      ((α k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (βU a)

namespace NatPair

variable {G : Type} [Group G] {U V V₁ W K : Subgroup G} {F : Type} [Field F]
  {α : ↥K →* SL(2, F)} {βV : ↥V →* Multiplicative (Fin 2 → F)}
  {βU : ↥U →* Multiplicative (Fin 2 → F)} (P : NatPair U V V₁ W K α βV βU)

include P

theorem conj_mem {X : Subgroup G} (hV₁X : V₁ ≤ X) (hXU : X ≤ U) {u x : G} (hu : u ∈ U)
    (hx : x ∈ X) : u * x * u⁻¹ ∈ X := by
  have h := X.mul_mem (hV₁X (P.hcomm u hu x (hXU hx))) hx
  simpa using h

theorem exists_dec {u : G} (hu : u ∈ U) : ∃ v ∈ V, ∃ w ∈ W, v * w = u := by
  let S : Subgroup G :=
    { carrier := {g | ∃ v ∈ V, ∃ w ∈ W, v * w = g}
      one_mem' := ⟨1, V.one_mem, 1, W.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨v, hv, w, hw, rfl⟩ ⟨v', hv', w', hw', rfl⟩
        refine ⟨v * v', V.mul_mem hv hv', v'⁻¹ * w * v'⁻¹⁻¹ * w', W.mul_mem ?_ hw', by group⟩
        exact P.conj_mem P.hV₁W P.hWU (U.inv_mem (P.hVU hv')) hw
      inv_mem' := by
        rintro _ ⟨v, hv, w, hw, rfl⟩
        refine ⟨w⁻¹ * v⁻¹ * w⁻¹⁻¹, ?_, w⁻¹, W.inv_mem hw, by group⟩
        exact P.conj_mem P.hV₁V P.hVU (U.inv_mem (P.hWU hw)) (V.inv_mem hv) }
  have hle : U ≤ S := by
    rw [← P.hWVU]
    refine sup_le (fun w hw => ⟨1, V.one_mem, w, hw, one_mul w⟩)
      (fun v hv => ⟨v, hv, 1, W.one_mem, mul_one v⟩)
  exact hle hu

@[expose] noncomputable def kappa (u : ↥U) : Fin 2 → F :=
  Multiplicative.toAdd (βV ⟨(P.exists_dec u.2).choose, (P.exists_dec u.2).choose_spec.1⟩)

theorem kappa_eq {u : ↥U} {v w : G} (hv : v ∈ V) (hw : w ∈ W) (h : v * w = (u : G)) :
    P.kappa u = Multiplicative.toAdd (βV ⟨v, hv⟩) := by
  obtain ⟨hv', w', hw', h'⟩ := (P.exists_dec u.2).choose_spec
  have h1 : (P.exists_dec u.2).choose⁻¹ * v ∈ W ⊓ V := by
    refine ⟨?_, V.mul_mem (V.inv_mem hv') hv⟩
    have e : (P.exists_dec u.2).choose⁻¹ * v = w' * w⁻¹ := by
      have e1 := h'.trans h.symm
      calc (P.exists_dec u.2).choose⁻¹ * v =
            (P.exists_dec u.2).choose⁻¹ * (v * w) * w⁻¹ := by group
        _ = (P.exists_dec u.2).choose⁻¹ * ((P.exists_dec u.2).choose * w') * w⁻¹ := by
          rw [e1]
        _ = w' * w⁻¹ := by group
    rw [e]
    exact W.mul_mem hw' (W.inv_mem hw)
  rw [P.hWV] at h1
  have h2 : βV (⟨_, hv'⟩⁻¹ * ⟨v, hv⟩) = 1 := by
    rw [← MonoidHom.mem_ker, P.hkerV]
    exact h1
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  exact congrArg Multiplicative.toAdd h2

theorem kappa_mul (a b : ↥U) : P.kappa (a * b) = P.kappa a + P.kappa b := by
  obtain ⟨v, hv, w, hw, hvw⟩ := P.exists_dec a.2
  obtain ⟨v', hv', w', hw', hvw'⟩ := P.exists_dec b.2
  have hw'' : v'⁻¹ * w * v' * w' ∈ W :=
    W.mul_mem (by simpa using P.conj_mem P.hV₁W P.hWU (U.inv_mem (P.hVU hv')) hw) hw'
  rw [P.kappa_eq hv hw hvw, P.kappa_eq hv' hw' hvw',
    P.kappa_eq (V.mul_mem hv hv') hw'' (by rw [Subgroup.coe_mul, ← hvw, ← hvw']; group)]
  rw [show (⟨v * v', V.mul_mem hv hv'⟩ : ↥V) = ⟨v, hv⟩ * ⟨v', hv'⟩ from rfl, map_mul, toAdd_mul]

theorem kappa_of_mem_V {v : G} (hv : v ∈ V) :
    P.kappa ⟨v, P.hVU hv⟩ = Multiplicative.toAdd (βV ⟨v, hv⟩) :=
  P.kappa_eq hv W.one_mem (mul_one v)

@[expose] noncomputable def X (u : ↥U) : (Fin 2 → F) × (Fin 2 → F) :=
  (P.kappa u, Multiplicative.toAdd (βU u))

theorem X_mul (a b : ↥U) : P.X (a * b) = P.X a + P.X b :=
  Prod.ext (P.kappa_mul a b) (by simp [X, map_mul, toAdd_mul])

theorem X_eq_zero_iff (u : ↥U) : P.X u = 0 ↔ (u : G) ∈ V₁ := by
  have hU : βU u = 1 ↔ (u : G) ∈ V := by
    rw [← MonoidHom.mem_ker, P.hkerU, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 : βU u = 1 := Multiplicative.toAdd.injective (congrArg Prod.snd h)
    have huV := hU.1 h1
    have h2 : P.kappa ⟨u, P.hVU huV⟩ = 0 := congrArg Prod.fst h
    rw [P.kappa_of_mem_V huV] at h2
    have h3 : βV ⟨u, huV⟩ = 1 := Multiplicative.toAdd.injective h2
    rw [← MonoidHom.mem_ker, P.hkerV, Subgroup.mem_subgroupOf] at h3
    exact h3
  · intro h
    have huV : (u : G) ∈ V := P.hV₁V h
    have h3 : βV ⟨u, huV⟩ = 1 := by
      rw [← MonoidHom.mem_ker, P.hkerV, Subgroup.mem_subgroupOf]
      exact h
    refine Prod.ext ?_ ?_
    · show P.kappa ⟨u, P.hVU huV⟩ = 0
      rw [P.kappa_of_mem_V huV, h3, toAdd_one]
    · show Multiplicative.toAdd (βU u) = 0
      rw [hU.2 huV, toAdd_one]

theorem X_conj_K (k : ↥K) (a b : ↥U) (hab : (b : G) = k * a * k⁻¹) :
    P.X b = (((α k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ (P.X a).1,
      ((α k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ (P.X a).2) := by
  obtain ⟨v, hv, w, hw, hvw⟩ := P.exists_dec a.2
  have hkv : (k : G) * v * (k : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (P.hKV k.2) v).mp hv
  have hkw : (k : G) * w * (k : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (P.hKW k.2) w).mp hw
  refine Prod.ext ?_ (P.eqU k a b hab)
  show P.kappa b = _ *ᵥ P.kappa a
  rw [P.kappa_eq hkv hkw (by rw [hab, ← hvw, Subgroup.coe_inv]; group), P.kappa_eq hv hw hvw]
  exact P.eqV k ⟨v, hv⟩ ⟨_, hkv⟩ rfl

theorem X_conj_U {t : G} (ht : t ∈ U) (a b : ↥U) (hab : (b : G) = t * a * t⁻¹) :
    P.X b = P.X a := by
  have hz : t * a * t⁻¹ * (a : G)⁻¹ ∈ U := U.mul_mem (U.mul_mem (U.mul_mem ht a.2) (U.inv_mem ht))
    (U.inv_mem a.2)
  have hb : b = ⟨_, hz⟩ * a := Subtype.ext (by rw [Subgroup.coe_mul, hab]; group)
  rw [hb, P.X_mul, (P.X_eq_zero_iff _).2 (P.hcomm t ht a a.2), zero_add]

theorem X_surjective : Function.Surjective P.X := by
  rintro ⟨x, y⟩
  obtain ⟨v, hv⟩ := P.hβV (Multiplicative.ofAdd x)
  obtain ⟨u₀, hu₀⟩ := P.hβU (Multiplicative.ofAdd y)
  obtain ⟨v₀, hv₀, w₀, hw₀, hvw₀⟩ := P.exists_dec u₀.2
  have hβw : βU ⟨w₀, P.hWU hw₀⟩ = Multiplicative.ofAdd y := by
    have h1 : βU ⟨v₀, P.hVU hv₀⟩ = 1 := by
      rw [← MonoidHom.mem_ker, P.hkerU, Subgroup.mem_subgroupOf]
      exact hv₀
    have h2 : u₀ = ⟨v₀, P.hVU hv₀⟩ * ⟨w₀, P.hWU hw₀⟩ := Subtype.ext hvw₀.symm
    rw [h2, map_mul, h1, one_mul] at hu₀
    exact hu₀
  have hβv : βU ⟨v, P.hVU v.2⟩ = 1 := by
    rw [← MonoidHom.mem_ker, P.hkerU, Subgroup.mem_subgroupOf]
    exact v.2
  refine ⟨⟨v, P.hVU v.2⟩ * ⟨w₀, P.hWU hw₀⟩, Prod.ext ?_ ?_⟩
  · show P.kappa _ = x
    rw [P.kappa_eq v.2 hw₀ rfl, hv, toAdd_ofAdd]
  · show Multiplicative.toAdd (βU _) = y
    rw [map_mul, hβv, one_mul, hβw, toAdd_ofAdd]

end NatPair

end CFSG.Quasithin.Vol2.Ch11.SecJ
