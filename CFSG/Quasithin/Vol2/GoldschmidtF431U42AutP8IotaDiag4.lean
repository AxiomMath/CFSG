module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaDiag3
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaBN4
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaDiag2

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

theorem iota_of_ahBN
    {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} (iso : AutIso M₁ M₂)
    {s t : Ah} {us ut : List Ah} (H : AhBN s t us ut)
    (hG : ((iso.toG1 ⟨s, H.s1⟩) * iso.toG2 ⟨t, H.t1⟩) ^ 4 = 1) :
    ∃ ι : Ah ≃* ↥(M₁ ⊔ M₂), (∀ x : ↥P1h, (ι (x : Ah) : G) = (iso.phi1 x : G)) ∧
      ∀ x : ↥P2h, (ι (x : Ah) : G) = (iso.phi2 x : G) := by
  classical
  set D : Subgroup (Ah × G) := Subgroup.closure
    (((gr1 iso).range : Set (Ah × G)) ∪ ((gr2 iso).range : Set (Ah × G))) with hD
  obtain ⟨R, hR135, hRcov⟩ := (bnPair_of_ahBN iso H hG).covering
  have hB' : Nat.card (grB iso).range = 384 := by
    rw [← card_Bh]
    exact (Nat.card_congr (MonoidHom.ofInjective (grB_injective iso)).toEquiv).symm
  have hDle : Nat.card D ≤ 51840 := by
    have hcov : ∀ x : D, ∃ r : ↥R, ((r : Ah × G)⁻¹ * (x : Ah × G)) ∈ (grB iso).range := fun x => by
      obtain ⟨r, hr, h⟩ := hRcov x.1 x.2
      exact ⟨⟨r, hr⟩, h⟩
    choose f hf using hcov
    let g : D → ↥R × ↥(grB iso).range := fun x =>
      (f x, ⟨((f x : Ah × G))⁻¹ * (x : Ah × G), hf x⟩)
    have hg : Function.Injective g := by
      intro x y hxy
      have h1 : f x = f y := congrArg Prod.fst hxy
      have h2 : ((f x : Ah × G))⁻¹ * (x : Ah × G) = ((f y : Ah × G))⁻¹ * (y : Ah × G) :=
        congrArg (fun p => (p.2 : Ah × G)) hxy
      rw [h1] at h2
      exact Subtype.ext (mul_left_cancel h2)
    calc Nat.card D ≤ Nat.card (↥R × ↥(grB iso).range) := Nat.card_le_card_of_injective g hg
      _ = Nat.card ↥R * Nat.card ↥(grB iso).range := Nat.card_prod _ _
      _ = R.card * 384 := by rw [Nat.card_eq_finsetCard, hB']
      _ ≤ 135 * 384 := Nat.mul_le_mul_right _ hR135
  let fstD : D →* Ah := (MonoidHom.fst Ah G).comp D.subtype
  have hfst : Function.Surjective fstD := by
    have hle : P1h ⊔ P2h ≤ D.map (MonoidHom.fst Ah G) := by
      refine sup_le ?_ ?_
      · intro x hx
        exact ⟨gr1 iso ⟨x, hx⟩, Subgroup.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩), rfl⟩
      · intro x hx
        exact ⟨gr2 iso ⟨x, hx⟩, Subgroup.subset_closure (Or.inr ⟨⟨x, hx⟩, rfl⟩), rfl⟩
    intro a
    have ha : a ∈ P1h ⊔ P2h := by rw [sup_P1h_P2h]; trivial
    obtain ⟨d, hd, rfl⟩ := hle ha
    exact ⟨⟨d, hd⟩, rfl⟩
  have hAh : Nat.card Ah = 51840 := card_A
  have hbij : Function.Bijective fstD := hfst.bijective_of_nat_card_le (by
    rw [hAh]
    exact hDle)
  let e0 : D ≃* Ah := MulEquiv.ofBijective fstD hbij
  let ρ : Ah →* G := (MonoidHom.snd Ah G).comp (D.subtype.comp e0.symm.toMonoidHom)
  have hρ1 : ∀ x : ↥P1h, ρ (x : Ah) = iso.toG1 x := by
    intro x
    have hmem : gr1 iso x ∈ D := Subgroup.subset_closure (Or.inl ⟨x, rfl⟩)
    have : e0.symm (x : Ah) = ⟨gr1 iso x, hmem⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show ((e0.symm (x : Ah) : D) : Ah × G).2 = _
    rw [this]
    rfl
  have hρ2 : ∀ x : ↥P2h, ρ (x : Ah) = iso.toG2 x := by
    intro x
    have hmem : gr2 iso x ∈ D := Subgroup.subset_closure (Or.inr ⟨x, rfl⟩)
    have : e0.symm (x : Ah) = ⟨gr2 iso x, hmem⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show ((e0.symm (x : Ah) : D) : Ah × G).2 = _
    rw [this]
    rfl
  have hinj : Function.Injective ρ := by
    refine (MonoidHom.ker_eq_bot_iff ρ).1 (eq_bot_of_normal ρ.ker ?_ ?_)
    · refine eq_bot_iff.2 fun x hx => ?_
      obtain ⟨hk, hx1⟩ := hx
      have h1 : iso.toG1 ⟨x, hx1⟩ = 1 := by rw [← hρ1 ⟨x, hx1⟩]; exact hk
      have : (⟨x, hx1⟩ : ↥P1h) = 1 := iso.toG1_injective (by rw [h1, map_one])
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
    · refine eq_bot_iff.2 fun x hx => ?_
      obtain ⟨hk, hx2⟩ := hx
      have h1 : iso.toG2 ⟨x, hx2⟩ = 1 := by rw [← hρ2 ⟨x, hx2⟩]; exact hk
      have : (⟨x, hx2⟩ : ↥P2h) = 1 := iso.toG2_injective (by rw [h1, map_one])
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hmapP1 : P1h.map ρ = M₁ := by
    ext m
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [show ρ x = iso.toG1 ⟨x, hx⟩ from hρ1 ⟨x, hx⟩]
      exact (iso.phi1 ⟨x, hx⟩).2
    · intro hm
      obtain ⟨y, hy⟩ := iso.phi1.surjective ⟨m, hm⟩
      refine ⟨y, y.2, ?_⟩
      rw [show ρ (y : Ah) = iso.toG1 y from hρ1 y]
      exact congrArg Subtype.val hy
  have hmapP2 : P2h.map ρ = M₂ := by
    ext m
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [show ρ x = iso.toG2 ⟨x, hx⟩ from hρ2 ⟨x, hx⟩]
      exact (iso.phi2 ⟨x, hx⟩).2
    · intro hm
      obtain ⟨y, hy⟩ := iso.phi2.surjective ⟨m, hm⟩
      refine ⟨y, y.2, ?_⟩
      rw [show ρ (y : Ah) = iso.toG2 y from hρ2 y]
      exact congrArg Subtype.val hy
  have hrange : ρ.range = M₁ ⊔ M₂ := by
    rw [MonoidHom.range_eq_map, ← sup_P1h_P2h, Subgroup.map_sup, hmapP1, hmapP2]
  have hle : ∀ a : Ah, ρ a ∈ M₁ ⊔ M₂ := fun a => hrange ▸ ⟨a, rfl⟩
  let ι : Ah ≃* ↥(M₁ ⊔ M₂) := MulEquiv.ofBijective (ρ.codRestrict (M₁ ⊔ M₂) hle)
    ⟨fun a b h => hinj (congrArg Subtype.val h), fun ⟨g, hg⟩ => by
      obtain ⟨a, ha⟩ := (hrange ▸ hg : g ∈ ρ.range)
      exact ⟨a, Subtype.ext ha⟩⟩
  exact ⟨ι, fun x => hρ1 x, fun x => hρ2 x⟩

end CFSG.Quasithin.H13.F431.U42Aut
