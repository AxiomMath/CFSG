module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueBasic
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace NoOffExc

open Multiplicative

variable {G : Type} [Group G]

theorem card_range_eq_card {V : Type*} [AddCommGroup V] {ι : Multiplicative V →* G}
    (hinj : Function.Injective ι) : Nat.card ι.range = Nat.card V :=
  (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem noOffender_of_modelAct [Finite G] {V : Type*} [AddCommGroup V] [Finite V] {W : Type*}
    [Group W] {p : ℕ} (ρ : W →* Equiv.Perm V) (hρ : Function.Injective ρ)
    (hW : ∀ A : Subgroup W, IsElemAbelian p A → A ≠ ⊥ →
      Nat.card A * Nat.card {v : V // ∀ a ∈ A, ρ a v = v} < Nat.card V)
    {ι : Multiplicative V →* G} (hinj : Function.Injective ι) {N Bs : Subgroup G}
    (hrange : ι.range = Bs)
    (hact : ∀ g ∈ N, g ∈ Subgroup.normalizer (Bs : Set G) → g ^ p = 1 →
      ∃ w : W, ∀ v : V, g * ι (ofAdd v) * g⁻¹ = ι (ofAdd (ρ w v))) :
    GGNoOffender p N Bs := by
  intro E hEN hEB hE
  have hdata : ∀ e : E, ∃ w : W, ∀ v : V,
      (e : G) * ι (ofAdd v) * (e : G)⁻¹ = ι (ofAdd (ρ w v)) :=
    fun e => hact e (hEN e.2) (hEB e.2) (hE.2 e e.2)
  choose w hw using hdata
  have huniq : ∀ (e : E) (u : W),
      (∀ v : V, (e : G) * ι (ofAdd v) * (e : G)⁻¹ = ι (ofAdd (ρ u v))) → w e = u := by
    intro e u hu
    apply hρ
    refine Equiv.ext fun v => ?_
    have h1 := hinj ((hw e v).symm.trans (hu v))
    exact congrArg toAdd h1
  let φ : E →* W :=
    { toFun := w
      map_one' := huniq 1 1 fun v => by simp
      map_mul' := fun e e' => huniq (e * e') (w e * w e') fun v => by
        calc ((e * e' : E) : G) * ι (ofAdd v) * ((e * e' : E) : G)⁻¹
            = (e : G) * ((e' : G) * ι (ofAdd v) * (e' : G)⁻¹) * (e : G)⁻¹ := by
              simp only [Subgroup.coe_mul, mul_inv_rev]
              group
          _ = ι (ofAdd (ρ (w e * w e') v)) := by
              rw [hw e', hw e, map_mul, Equiv.Perm.mul_apply] }
  have hφ : ∀ (e : E) (v : V), (e : G) * ι (ofAdd v) * (e : G)⁻¹ = ι (ofAdd (ρ (φ e) v)) :=
    hw
  have hker1 : ∀ e : E, φ e = 1 → ∀ b ∈ Bs, (e : G) * b = b * e := by
    intro e he b hb
    rw [← hrange] at hb
    obtain ⟨t, rfl⟩ := hb
    have h1 := hφ e (toAdd t)
    rw [he, map_one, Equiv.Perm.coe_one, id, ofAdd_toAdd] at h1
    calc (e : G) * ι t = (e : G) * ι t * (e : G)⁻¹ * e := by group
      _ = ι t * e := by rw [h1]
  have hAel : IsElemAbelian p φ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, e, rfl⟩ := a
      obtain ⟨_, e', rfl⟩ := b
      apply Subtype.ext
      change φ e * φ e' = φ e' * φ e
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (TableB.IsElemAbelian.comm hE e.2 e'.2)
    · rintro _ ⟨e, rfl⟩
      have hep : e ^ p = 1 := Subtype.ext (by simpa using hE.2 e e.2)
      rw [← map_pow, hep, map_one]
  by_cases hA : φ.range = ⊥
  · left
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : φ ⟨e, he⟩ = 1 := by
      have : φ ⟨e, he⟩ ∈ φ.range := ⟨_, rfl⟩
      rwa [hA, Subgroup.mem_bot] at this
    exact (hker1 ⟨e, he⟩ h1 b hb).symm
  right
  have hcount := hW φ.range hAel hA
  have hfix : ∀ v : V, ι (ofAdd v) ∈ Subgroup.centralizer (E : Set G) ↔
      ∀ a ∈ φ.range, ρ a v = v := by
    intro v
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · rintro h _ ⟨e, rfl⟩
      have h1 : (e : G) * ι (ofAdd v) * (e : G)⁻¹ = ι (ofAdd v) := by
        rw [h e e.2, mul_inv_cancel_right]
      exact congrArg toAdd (hinj ((hφ e v).symm.trans h1))
    · intro h e he
      have h1 := hφ ⟨e, he⟩ v
      rw [h _ ⟨⟨e, he⟩, rfl⟩] at h1
      calc e * ι (ofAdd v) = e * ι (ofAdd v) * e⁻¹ * e := by group
        _ = ι (ofAdd v) * e := by rw [h1]
  have hCF : Nat.card (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) =
      Nat.card {v : V // ∀ a ∈ φ.range, ρ a v = v} := by
    refine (Nat.card_congr (Equiv.ofBijective
      (fun v : {v : V // ∀ a ∈ φ.range, ρ a v = v} =>
        (⟨ι (ofAdd (v : V)), hrange ▸ ⟨_, rfl⟩, (hfix v).mpr v.2⟩ :
          (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G)))
      ⟨fun v v' h => ?_, fun b => ?_⟩)).symm
    · exact Subtype.ext (by simpa using hinj (congrArg Subtype.val h))
    · obtain ⟨t, ht⟩ : (b : G) ∈ ι.range := hrange ▸ b.2.1
      have hb : ι (ofAdd (toAdd t)) ∈ Subgroup.centralizer (E : Set G) := by
        rw [ofAdd_toAdd, ht]
        exact b.2.2
      refine ⟨⟨toAdd t, (hfix _).mp hb⟩, Subtype.ext ?_⟩
      change ι (ofAdd (toAdd t)) = b
      rw [ofAdd_toAdd, ht]
  have hker : Nat.card φ.ker ≤ Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) := by
    refine Nat.card_le_card_of_injective
      (fun k : φ.ker => (⟨((k : E) : G), (k : E).2, Subgroup.mem_centralizer_iff.mpr
        fun b hb => (hker1 k k.2 b hb).symm⟩ :
          (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G))) fun k k' h => ?_
    have h' := congrArg (fun y : (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) =>
      (y : G)) h
    exact Subtype.ext (Subtype.ext h')
  have hE' := Subgroup.card_ker_mul_card_range φ
  have hBs : Nat.card Bs = Nat.card V := by rw [← hrange, card_range_eq_card hinj]
  have hpos : 0 < Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) := Nat.card_pos
  rw [hCF, hBs, ← hE']
  calc Nat.card {v : V // ∀ a ∈ φ.range, ρ a v = v} * (Nat.card φ.ker * Nat.card φ.range)
      ≤ Nat.card {v : V // ∀ a ∈ φ.range, ρ a v = v} *
          (Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) * Nat.card φ.range) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hker)
    _ = Nat.card φ.range * Nat.card {v : V // ∀ a ∈ φ.range, ρ a v = v} *
          Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) := by ring
    _ < Nat.card V * Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) :=
        Nat.mul_lt_mul_of_pos_right hcount hpos

theorem noOffender_of_centralize {p : ℕ} {N Bs : Subgroup G}
    (h : ∀ g ∈ N, g ∈ Subgroup.normalizer (Bs : Set G) → g ^ p = 1 →
      g ∈ Subgroup.centralizer (Bs : Set G)) :
    GGNoOffender p N Bs :=
  fun _ hEN hEB hE => Or.inl fun e he => h e (hEN he) (hEB he) (hE.2 e he)

end NoOffExc

end CFSG.StandardType
