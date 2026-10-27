module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtFin1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChLat2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.At

open S35.Std S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem inf_eq_bot_of_card_two {Z V : Subgroup G} (hZ : Nat.card Z = 2) (h : ¬ Z ≤ V) :
    Z ⊓ V = ⊥ := by
  have : Fact (Nat.Prime (Nat.card Z)) := ⟨hZ ▸ Nat.prime_two⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((Z ⊓ V).subgroupOf Z) with h1 | h1
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : ↥Z) ∈ (Z ⊓ V).subgroupOf Z := hx
    rw [h1] at this
    have h2 := Subgroup.mem_bot.mp this
    have : x = 1 := congrArg Subtype.val h2
    simp [this]
  · exact absurd (fun x hx => by
      have : (⟨x, hx⟩ : ↥Z) ∈ (Z ⊓ V).subgroupOf Z := by rw [h1]; trivial
      exact (Subgroup.mem_inf.mp this).2) h

omit [Finite G] in
theorem relIndex_sup_eq_of_comm {A C Z : Subgroup G} (hA : IsMulCommutative A) (hC : C ≤ A)
    (hZ : Z ≤ A) : Z.relIndex (C ⊔ Z) = Z.relIndex C := by
  have : ((Z.subgroupOf A)).Normal := S34.normal_subgroupOf_of_comm hA Z
  have h1 := Subgroup.relIndex_sup_right (H := C.subgroupOf A) (K := Z.subgroupOf A)
  rw [← Subgroup.subgroupOf_sup hC hZ, Subgroup.relIndex_subgroupOf (sup_le hC hZ),
    Subgroup.relIndex_subgroupOf hC] at h1
  exact h1

theorem inf_eq_bot_iff_relIndex {Z C : Subgroup G} :
    Z ⊓ C = ⊥ ↔ Z.relIndex C = Nat.card C := by
  constructor
  · intro hb
    rw [← Subgroup.inf_relIndex_right, hb, Subgroup.relIndex_bot_left]
  · intro hr
    have h := Subgroup.card_mul_index ((Z ⊓ C).subgroupOf C)
    have h2 : ((Z ⊓ C).subgroupOf C).index = Z.relIndex C := by
      rw [← Subgroup.inf_relIndex_right]; rfl
    rw [h2, hr] at h
    have hpos : 0 < Nat.card C := Nat.card_pos
    have h1 : Nat.card ((Z ⊓ C).subgroupOf C) = 1 := by
      have := Nat.eq_of_mul_eq_mul_right hpos (h.trans (one_mul _).symm)
      exact this
    rw [Subgroup.card_eq_one] at h1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.2⟩ : ↥C) ∈ (Z ⊓ C).subgroupOf C := hx
    rw [h1] at this
    have h3 : x = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp this)
    simp [h3]

omit [Finite G] in
theorem zc_mul_self {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    zc D * zc D = 1 := by
  obtain ⟨g, -, -, hz, -⟩ := std_data hD
  have h2 : zStd * zStd = 1 := by unfold zStd; decide +kernel
  rw [hz]
  calc g * zStd * g⁻¹ * (g * zStd * g⁻¹) = g * (zStd * zStd) * g⁻¹ := by group
    _ = 1 := by rw [h2]; group

theorem relIndex_le_card' (X Y : Subgroup G) : X.relIndex Y ≤ Nat.card Y := by
  have h := Subgroup.card_mul_index (X.subgroupOf Y)
  have h1 : 0 < Nat.card (X.subgroupOf Y) := Nat.card_pos
  unfold Subgroup.relIndex
  nlinarith

theorem card_bar_eq (hS : Sit H M S) {δ : Geo H M} (c : Ch.Chart δ) (hδ : vtype δ = false)
    {A : Subgroup G} (hA : A ≤ stab δ) : Nat.card (c.bar A) = (Qv δ).relIndex A := by
  have := Subgroup.relIndex_ker (K := A.subgroupOf (stab δ)) c.θ
  rw [c.ker_eq_Qv hS hδ, Subgroup.relIndex_subgroupOf hA] at this
  exact this.symm

theorem four_le_relIndex_Qv (hS : Sit H M S) {β α' : Geo H M} (hp : S34.PD β α')
    (c : Ch.Chart α') {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {v : G}
    (hv : v ∈ Vn β) (hvs : v ∈ stab α') (hz : c.θ ⟨v, hvs⟩ = zc D)
    (h1 : ∀ u ∈ Vn α' ⊓ Qv β, ⁅v, u⁆ = 1) : 4 ≤ (Qv β).relIndex (Vn α') := by
  have hmem : ∀ u ∈ Vn α', ⁅v, u⁆ ∈ Vn α' := fun u hu => by
    have := (PD_comm_le hS hp) (Subgroup.commutator_mem_commutator hv hu)
    exact this.2
  let f : ↥(Vn α') →* orth.W := MonoidHom.mk' (fun u => c.π ⟨⁅v, (u : G)⁆, hmem u u.2⟩) (by
    intro u1 u2
    have e : (⟨⁅v, ((u1 * u2 : ↥(Vn α')) : G)⁆, hmem _ (u1 * u2).2⟩ : ↥(Vn α')) =
        ⟨⁅v, (u1 : G)⁆, hmem _ u1.2⟩ * ⟨⁅v, (u2 : G)⁆, hmem _ u2.2⟩ := by
      apply Subtype.ext
      show ⁅v, (u1 : G) * u2⁆ = ⁅v, (u1 : G)⁆ * ⁅v, (u2 : G)⁆
      have hab := F7.isElemAbelian_comm (Vn_isElemAbelian hS α') u1.2 (hmem _ u2.2)
      calc ⁅v, (u1 : G) * u2⁆ = ⁅v, (u1 : G)⁆ * ((u1 : G) * ⁅v, (u2 : G)⁆ * (u1 : G)⁻¹) := by
            simp only [commutatorElement_def]; group
        _ = ⁅v, (u1 : G)⁆ * ⁅v, (u2 : G)⁆ := by rw [hab]; simp
    show c.π _ = c.π _ * c.π _
    rw [e, map_mul])
  have hD4 : Nat.card (commW orth (Subgroup.zpowers (zc D)) ⊤) = 4 := by
    rw [← commW_That_eq hD]; exact card_commW_That hD
  have hrange : commW orth (Subgroup.zpowers (zc D)) ⊤ ≤ f.range := by
    rw [commW_zpowers_top, Subgroup.closure_le]
    rintro w ⟨u, rfl⟩
    obtain ⟨u', rfl⟩ := c.π_surj u
    refine ⟨u', ?_⟩
    have e : (⟨⁅v, (u' : G)⁆, hmem u' u'.2⟩ : ↥(Vn α')) =
        Ch.conjV ⟨v, hvs⟩ u' * u'⁻¹ := by
      apply Subtype.ext
      simp [commutatorElement_def, mul_assoc]
    show c.π ⟨⁅v, (u' : G)⁆, hmem u' u'.2⟩ = _
    rw [e, map_mul, map_inv, c.π_conj, hz]
  have hker : (Vn α' ⊓ Qv β).subgroupOf (Vn α') ≤ f.ker := by
    intro u hu
    rw [MonoidHom.mem_ker]
    have h := h1 u hu
    show c.π ⟨⁅v, (u : G)⁆, hmem u u.2⟩ = 1
    have : (⟨⁅v, (u : G)⁆, hmem u u.2⟩ : ↥(Vn α')) = 1 := Subtype.ext h
    rw [this, map_one]
  have h4 : 4 ≤ Nat.card f.range := hD4 ▸ Subgroup.card_le_of_le hrange
  rw [← Subgroup.index_ker] at h4
  refine h4.trans ((Subgroup.index_antitone hker).trans ?_)
  rw [← Subgroup.inf_relIndex_left (H := Vn α') (K := Qv β), inf_comm]
  exact le_rfl

end S35.At

end F53.Stellmacher

end CFSG.Quasithin
