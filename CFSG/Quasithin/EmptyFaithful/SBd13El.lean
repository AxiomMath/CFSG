module

public import CFSG.Quasithin.EmptyFaithful.R3c14Cfg
public import CFSG.Quasithin.Background.F420Basic

public section

namespace CFSG.Quasithin.SBd13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.R3c14 CFSG.Quasithin.F420

variable {X : Type} [Group X]

@[reducible] def conjAct {T V : Subgroup X} (hTV : T ≤ Subgroup.normalizer (V : Set X)) :
    MulAction ↥T ↥V where
  smul t v := ⟨(t : X) * v * (t : X)⁻¹, (Subgroup.mem_normalizer_iff.1 (hTV t.2) v).1 v.2⟩
  one_smul v := Subtype.ext (show (1 : X) * v * 1⁻¹ = v by simp)
  mul_smul s t v := Subtype.ext (show ((s : X) * t) * v * ((s : X) * t)⁻¹ =
    s * (t * v * (t : X)⁻¹) * (s : X)⁻¹ by group)

theorem exists_fixed_ne_one [Finite X] {T V : Subgroup X} (hT : IsPGroup 2 T)
    (hTV : T ≤ Subgroup.normalizer (V : Set X)) (hV4 : Nat.card V = 4) :
    ∃ v ∈ V, v ≠ 1 ∧ ∀ t ∈ T, v * t = t * v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction ↥T ↥V := conjAct hTV
  have h1 := hT.card_modEq_card_fixedPoints ↥V
  rw [hV4] at h1
  have hone : (1 : ↥V) ∈ MulAction.fixedPoints ↥T ↥V := fun t =>
    Subtype.ext (show (t : X) * 1 * (t : X)⁻¹ = 1 by simp)
  have hpos : 0 < Nat.card (MulAction.fixedPoints ↥T ↥V) := by
    rw [Nat.card_pos_iff]
    exact ⟨⟨⟨1, hone⟩⟩, inferInstance⟩
  have hge : 2 ≤ Nat.card (MulAction.fixedPoints ↥T ↥V) := by
    have h2 : (4 : ℕ) ≡ Nat.card (MulAction.fixedPoints ↥T ↥V) [MOD 2] := h1
    have h3 : Nat.card (MulAction.fixedPoints ↥T ↥V) % 2 = 0 := by
      have := h2.symm
      simpa [Nat.ModEq] using this
    omega
  have : Fintype (MulAction.fixedPoints ↥T ↥V) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at hge
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.1 (by omega : 1 < Fintype.card (MulAction.fixedPoints ↥T ↥V))
  have key : ∀ w : MulAction.fixedPoints ↥T ↥V, ∀ t ∈ T, ((w : ↥V) : X) * t = t * ((w : ↥V) : X) := by
    intro w t ht
    have h := congrArg (fun z : ↥V => (z : X)) (w.2 ⟨t, ht⟩)
    have h' : (t : X) * ((w : ↥V) : X) * (t : X)⁻¹ = ((w : ↥V) : X) := h
    calc ((w : ↥V) : X) * t = (t * ((w : ↥V) : X) * (t : X)⁻¹) * t := by rw [h']
      _ = t * ((w : ↥V) : X) := by group
  by_cases ha : ((a : ↥V) : X) = 1
  · refine ⟨((b : ↥V) : X), (b : ↥V).2, ?_, key b⟩
    intro hb
    exact hab (Subtype.ext (Subtype.ext (ha.trans hb.symm)))
  · exact ⟨((a : ↥V) : X), (a : ↥V).2, ha, key a⟩

theorem not_elConfig_of_inner [Finite X]
    (hinner : ∀ S : Subgroup X, quasithinIsSylowTwo S → ∀ α : MulAut X, (∀ s ∈ S, α s = s) →
      ∃ x : X, ∀ y : X, α y = x⁻¹ * y * x)
    (hW : SmallCentralizerWitness X) : ¬ ElConfig X := by
  rintro ⟨T, V, H, ζ, hT, hd⟩
  have hTS : quasithinIsSylowTwo T := by
    obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT
    exact ⟨hp, hi⟩
  obtain ⟨x, hx⟩ := hinner T hTS ζ hd.fixT
  have hcomm : ∀ s : X, ζ s = s → x * s = s * x := by
    intro s hs
    have h1 : x⁻¹ * s * x = s := (hx s).symm.trans hs
    calc x * s = x * (x⁻¹ * s * x) := by rw [h1]
      _ = s * x := by group
  have hxT : ∀ t ∈ T, x * t = t * x := fun t ht => hcomm t (hd.fixT t ht)
  have hxH : ∀ h ∈ H, x * h = h * x := fun h hh => hcomm h (hd.fixH h hh)
  have hx1 : x ≠ 1 := by
    intro h
    apply hd.ne
    ext y
    rw [hx y, h]
    simp
  obtain ⟨v₀, hv₀V, hv₀1, hv₀T⟩ := exists_fixed_ne_one hTS.1 hd.TV hd.V4
  rcases centralizer_le_two hW hTS x v₀ hxT hv₀T with h | h | h
  · exact hx1 h
  · exact hv₀1 h
  · refine hv₀1 (hd.fix v₀ hv₀V fun k hk => ?_)
    rw [← h]
    exact (hxH k hk).symm

end CFSG.Quasithin.SBd13
