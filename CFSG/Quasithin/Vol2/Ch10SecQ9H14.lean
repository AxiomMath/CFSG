module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch10SecQ9G8
public import CFSG.Quasithin.Vol2.Ch10StatementsE

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix CFSG.QuasithinUnique

abbrev o2Of (X : Subgroup SL4) : Subgroup SL4 := (CFSG.pCore 2 ↥X).map X.subtype

theorem card_o2Of (X : Subgroup SL4) : Nat.card (o2Of X) = Nat.card (CFSG.pCore 2 ↥X) :=
  Subgroup.card_map_of_injective X.subtype_injective

theorem card_X_eq (X : Subgroup SL4)
    (e : ↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    Nat.card X = Nat.card (o2Of X) * 168 := by
  rw [card_o2Of, Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥X),
    Nat.card_congr e.toEquiv, card_SL_three_two, mul_comm]

theorem le_o2Of (X : Subgroup SL4) {N : Subgroup SL4} (hNX : N ≤ X)
    (hN : X ≤ Subgroup.normalizer (N : Set SL4)) (hp : IsPGroup 2 N) : N ≤ o2Of X := by
  have hnorm : (N.subgroupOf X).Normal :=
    ⟨fun n hn x => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hN x.2) n).mp hn⟩
  have hp' : IsPGroup 2 (N.subgroupOf X) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hNX).symm
  have hle : N.subgroupOf X ≤ CFSG.pCore 2 ↥X := le_sSup ⟨hnorm, hp'⟩
  intro n hn
  exact ⟨⟨n, hNX hn⟩, hle (Subgroup.mem_subgroupOf.mpr hn), rfl⟩

theorem o2Of_le (X : Subgroup SL4) : o2Of X ≤ X := Subgroup.map_subtype_le _

theorem isPGroup_o2Of (X : Subgroup SL4) : IsPGroup 2 (o2Of X) :=
  CFSG.pCore_isPGroup.map _

theorem le_normalizer_o2Of (X : Subgroup SL4) :
    X ≤ Subgroup.normalizer (o2Of X : Set SL4) := by
  have h := Subgroup.le_normalizer_map (H := CFSG.pCore 2 ↥X) X.subtype
  have hn : Subgroup.normalizer (CFSG.pCore 2 ↥X : Set ↥X) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr CFSG.pCore_normal
  rwa [hn, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h

theorem conj_o2Of_le {X : Subgroup SL4} {s : SL4} (hs : s ∈ Subgroup.normalizer (X : Set SL4))
    {q : SL4} (hq : q ∈ o2Of X) : s * q * s⁻¹ ∈ o2Of X := by
  set N := (o2Of X).map (MulAut.conj s).toMonoidHom
  have hNX : N ≤ X := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hs y).mp (o2Of_le X hy)
  have hXN : X ≤ Subgroup.normalizer (N : Set SL4) := by
    intro x hx
    have hx' : s⁻¹ * x * s ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hs) x).mp hx
      rwa [inv_inv] at this
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(s⁻¹ * x * s) * y * (s⁻¹ * x * s)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_o2Of X hx') y).mp hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro ⟨y, hy, hyz⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyz
      refine ⟨(s⁻¹ * x * s)⁻¹ * y * (s⁻¹ * x * s), ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_o2Of X (X.inv_mem hx')) y).mp hy
        rwa [inv_inv] at this
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc s * ((s⁻¹ * x * s)⁻¹ * y * (s⁻¹ * x * s)) * s⁻¹
            = x⁻¹ * (s * y * s⁻¹) * x := by group
          _ = z := by rw [hyz]; group
  have hp : IsPGroup 2 N := (isPGroup_o2Of X).map _
  exact le_o2Of X hNX hXN hp ⟨q, hq, rfl⟩

theorem le_normalizer_o2Of_of {X S : Subgroup SL4} (hSX : S ≤ Subgroup.normalizer (X : Set SL4)) :
    S ≤ Subgroup.normalizer (o2Of X : Set SL4) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro q
  refine ⟨conj_o2Of_le (hSX hs), fun h => ?_⟩
  have := conj_o2Of_le (Subgroup.inv_mem _ (hSX hs)) h
  rwa [show s⁻¹ * (s * q * s⁻¹) * s⁻¹⁻¹ = q by group] at this

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
