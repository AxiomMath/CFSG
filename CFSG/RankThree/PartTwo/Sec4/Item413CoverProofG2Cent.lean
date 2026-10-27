module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofG2
public import CFSG.RankThree.PartTwo.Sec4.Item413CoverProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint

namespace Res417Five

@[expose] def K417G2TorusSep : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ChevalleyExceptionalModel Y .G2 3 1 →
    ∀ F T : Subgroup Y, CFSG.Assembly.IsElemAbelian 3 F → Nat.card F = 9 → IsPGroup 2 T →
      F ≤ Subgroup.normalizer (T : Set Y) → ¬ T ≤ Subgroup.centralizer (F : Set Y) →
      ∃ r₁ r₂ h h' : Y, r₁ * r₂ = r₂ * r₁ ∧ r₁ ^ 3 = 1 ∧ r₂ ^ 3 = 1 ∧
        Nat.card (Subgroup.closure ({r₁, r₂} : Set Y)) = 9 ∧
        Subgroup.closure ({r₁, r₂} : Set Y) ⊓ F = ⊥ ∧
        (∀ f ∈ F, f * r₁ = r₁ * f ∧ f * r₂ = r₂ * f) ∧
        (∀ f ∈ F, h * f * h⁻¹ = f) ∧ h * r₁ * h⁻¹ = r₁⁻¹ ∧ h * r₂ * h⁻¹ = r₂⁻¹ ∧
        h' * r₁ * h'⁻¹ = r₁ ∧ h' * r₂ * h'⁻¹ = r₂⁻¹

namespace SepCover

variable {K : Type*} [Group K]

theorem commutator_mul_central {a b z₁ z₂ : K} (h₁ : ∀ x : K, x * z₁ = z₁ * x)
    (h₂ : ∀ x : K, x * z₂ = z₂ * x) :
    a * z₁ * (b * z₂) * (a * z₁)⁻¹ * (b * z₂)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  calc a * z₁ * (b * z₂) * (a * z₁)⁻¹ * (b * z₂)⁻¹
      = a * (z₁ * b) * z₂ * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by group
    _ = a * (b * z₁) * z₂ * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by rw [← h₁ b]
    _ = a * b * (z₁ * z₂) * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by group
    _ = a * b * (z₂ * z₁) * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by rw [← h₁ z₂]
    _ = a * b * (z₂ * a⁻¹) * z₂⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z₂) * z₂⁻¹ * b⁻¹ := by rw [← h₂ a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutator_inv_right {a b : K} (h : ∀ x : K, x * (a * b * a⁻¹ * b⁻¹) =
    (a * b * a⁻¹ * b⁻¹) * x) : a * b⁻¹ * a⁻¹ * b⁻¹⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by
  have h' : ∀ x : K, x * (a * b * a⁻¹ * b⁻¹)⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ * x := fun x => by
    calc x * (a * b * a⁻¹ * b⁻¹)⁻¹
        = (a * b * a⁻¹ * b⁻¹)⁻¹ * ((a * b * a⁻¹ * b⁻¹) * x) * (a * b * a⁻¹ * b⁻¹)⁻¹ := by
          group
      _ = (a * b * a⁻¹ * b⁻¹)⁻¹ * (x * (a * b * a⁻¹ * b⁻¹)) * (a * b * a⁻¹ * b⁻¹)⁻¹ := by
          rw [← h x]
      _ = (a * b * a⁻¹ * b⁻¹)⁻¹ * x := by group
  calc a * b⁻¹ * a⁻¹ * b⁻¹⁻¹ = b⁻¹ * ((a * b * a⁻¹ * b⁻¹)⁻¹ * b) := by group
    _ = b⁻¹ * (b * (a * b * a⁻¹ * b⁻¹)⁻¹) := by rw [h' b]
    _ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by group

theorem eq_one_of_eq_inv {c : K} (h3 : c ^ 3 = 1) (hc : c = c⁻¹) : c = 1 := by
  have h2 : c * c = 1 := by
    calc c * c = c * c⁻¹ := by rw [← hc]
      _ = 1 := mul_inv_cancel c
  calc c = c ^ 3 * (c * c)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, one_mul]

variable {Q : Type*} [Group Q]

theorem commute_of_sep (π : K →* Q) (hker : π.ker ≤ Subgroup.center K)
    (hZ3 : ∀ z ∈ π.ker, z ^ 3 = 1) {u v g : K} (huv : π u * π v = π v * π u)
    (hgu : π g * π u * (π g)⁻¹ = π u) (hgv : π g * π v * (π g)⁻¹ = (π v)⁻¹) :
    u * v = v * u := by
  have hcen : ∀ z ∈ π.ker, ∀ x : K, x * z = z * x := fun z hz x =>
    Subgroup.mem_center_iff.mp (hker hz) x
  have hcZ : u * v * u⁻¹ * v⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, huv]
    group
  have hz₁ : u⁻¹ * (g * u * g⁻¹) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hgu, inv_mul_cancel]
  have hz₂ : v * (g * v * g⁻¹) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hgv, mul_inv_cancel]
  have e₁ : g * u * g⁻¹ = u * (u⁻¹ * (g * u * g⁻¹)) := by group
  have e₂ : g * v * g⁻¹ = v⁻¹ * (v * (g * v * g⁻¹)) := by group
  have hgc : g * (u * v * u⁻¹ * v⁻¹) * g⁻¹ = u * v * u⁻¹ * v⁻¹ := by
    rw [hcen _ hcZ g, mul_inv_cancel_right]
  have key : g * (u * v * u⁻¹ * v⁻¹) * g⁻¹ =
      (g * u * g⁻¹) * (g * v * g⁻¹) * (g * u * g⁻¹)⁻¹ * (g * v * g⁻¹)⁻¹ := by group
  rw [hgc, e₁, e₂, commutator_mul_central (hcen _ hz₁) (hcen _ hz₂),
    commutator_inv_right (fun x => hcen _ hcZ x)] at key
  have h1 := eq_one_of_eq_inv (hZ3 _ hcZ) key
  calc u * v = u * v * u⁻¹ * v⁻¹ * (v * u) := by group
    _ = v * u := by rw [h1, one_mul]

theorem pow_three_eq_one_of_inv (π : K →* Q) (hker : π.ker ≤ Subgroup.center K)
    (hZ3 : ∀ z ∈ π.ker, z ^ 3 = 1) {u g : K} (hu3 : π u ^ 3 = 1)
    (hgu : π g * π u * (π g)⁻¹ = (π u)⁻¹) : u ^ 3 = 1 := by
  have hcen : ∀ z ∈ π.ker, ∀ x : K, x * z = z * x := fun z hz x =>
    Subgroup.mem_center_iff.mp (hker hz) x
  have hw : u ^ 3 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hu3]
  have hz : u * (g * u * g⁻¹) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hgu, mul_inv_cancel]
  have e : g * u * g⁻¹ = u⁻¹ * (u * (g * u * g⁻¹)) := by group
  have hgw : g * u ^ 3 * g⁻¹ = u ^ 3 := by rw [hcen _ hw g, mul_inv_cancel_right]
  have hcomm : Commute u⁻¹ (u * (g * u * g⁻¹)) := hcen _ hz u⁻¹
  have key : g * u ^ 3 * g⁻¹ = (g * u * g⁻¹) ^ 3 := (conj_pow).symm
  rw [hgw, e, hcomm.mul_pow, hZ3 _ hz, mul_one, inv_pow] at key
  exact eq_one_of_eq_inv (hZ3 _ hw) key

end SepCover

open SepCover

theorem k417G2CoverCent_of (hS : K417G2TorusSep) : K417G2CoverCent := by
  intro H _ _ X F T hXq hZ3 hM hFe hF9 hFN hinner hFC hTX hT2 hFT hTF
  have hZ3' : ∀ z ∈ Subgroup.center X, z ^ 3 = 1 := fun z hz => by
    have h := pow_card_eq_one' (G := Subgroup.center X) (x := ⟨z, hz⟩)
    rw [hZ3] at h
    exact congrArg Subtype.val h
  obtain ⟨π, hπ⟩ : ∃ π : X →* X ⧸ Subgroup.center X,
      π = QuotientGroup.mk' (Subgroup.center X) := ⟨_, rfl⟩
  have hker : π.ker = Subgroup.center X := by rw [hπ, QuotientGroup.ker_mk']
  have hsurj : Function.Surjective π := by
    rw [hπ]
    exact QuotientGroup.mk'_surjective _
  have hkerZ : π.ker ≤ Subgroup.center X := hker.le
  have hker3 : ∀ z ∈ π.ker, z ^ 3 = 1 := fun z hz => hZ3' z (hker ▸ hz)
  have hsame : ∀ a b : X, (∀ y ∈ X, (a : H) * y * (a : H)⁻¹ = (b : H) * y * (b : H)⁻¹) →
      π a = π b := by
    intro a b hab
    have hc : a⁻¹ * b ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have h1 := hab y y.2
      calc (y : H) * ((a : H)⁻¹ * b) = (a : H)⁻¹ * ((a : H) * y * (a : H)⁻¹) * b := by group
        _ = (a : H)⁻¹ * ((b : H) * y * (b : H)⁻¹) * b := by rw [h1]
        _ = (a : H)⁻¹ * b * y := by group
    have h1 : π (a⁻¹ * b) = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hc
    rwa [map_mul, map_inv, inv_mul_eq_one] at h1
  choose xf hxfX hxf using hinner
  set xF : F → X := fun f => ⟨xf f f.2, hxfX f f.2⟩ with hxF
  have hact : ∀ f : F, ∀ y ∈ X, (f : H) * y * (f : H)⁻¹ = (xF f : H) * y * (xF f : H)⁻¹ :=
    fun f => hxf f f.2
  let η : F →* X ⧸ Subgroup.center X := MonoidHom.mk' (fun f => π (xF f)) (fun f₁ f₂ => by
    show π (xF (f₁ * f₂)) = π (xF f₁) * π (xF f₂)
    rw [← map_mul]
    apply hsame
    intro y hy
    have hy₂ : (f₂ : H) * y * (f₂ : H)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hFN f₂.2) y).mp hy
    have h12 := hact (f₁ * f₂) y hy
    rw [Subgroup.coe_mul] at h12
    rw [← h12, Subgroup.coe_mul]
    calc (f₁ : H) * f₂ * y * ((f₁ : H) * f₂)⁻¹ = f₁ * (f₂ * y * (f₂ : H)⁻¹) * (f₁ : H)⁻¹ := by
          group
      _ = xF f₁ * (f₂ * y * (f₂ : H)⁻¹) * (xF f₁ : H)⁻¹ := hact f₁ _ hy₂
      _ = xF f₁ * (xF f₂ * y * (xF f₂ : H)⁻¹) * (xF f₁ : H)⁻¹ := by rw [hact f₂ y hy]
      _ = (xF f₁ : H) * xF f₂ * y * ((xF f₁ : H) * xF f₂)⁻¹ := by group)
  have hη : ∀ f : F, η f = π (xF f) := fun f => rfl
  have hηinj : Function.Injective η := by
    rw [injective_iff_map_eq_one]
    intro f hf
    rw [hη, ← MonoidHom.mem_ker, hker] at hf
    have hfC : (f : H) ∈ Subgroup.centralizer (X : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := hact f y hy
      have h2 : (y : H) * xF f = xF f * y :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hf ⟨y, hy⟩)
      have h3 : (f : H) * y * (f : H)⁻¹ = y := by rw [h1, ← h2, mul_inv_cancel_right]
      calc y * (f : H) = f * y * (f : H)⁻¹ * f := by rw [h3]
        _ = f * y := by group
    have h1 : (f : H) ∈ F ⊓ Subgroup.centralizer (X : Set H) := ⟨f.2, hfC⟩
    rw [hFC, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hFe' : CFSG.Assembly.IsElemAbelian 3 η.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨f₁, hf₁⟩ := a.2
      obtain ⟨f₂, hf₂⟩ := b.2
      apply Subtype.ext
      change (a : X ⧸ Subgroup.center X) * b = b * a
      rw [← hf₁, ← hf₂, ← map_mul, ← map_mul, hFe.1.1.comm f₁ f₂]
    · obtain ⟨f, rfl⟩ := hy
      have hf3 : f ^ 3 = 1 := Subtype.ext (by simpa using hFe.2 f f.2)
      rw [← map_pow, hf3, map_one]
  have hF9' : Nat.card η.range = 9 := by
    rw [← hF9]
    exact (Nat.card_congr (MonoidHom.ofInjective hηinj).toEquiv).symm
  have hT2' : IsPGroup 2 ((T.subgroupOf X).map π) :=
    (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm).map π
  have hxN : ∀ f : F, xF f ∈ Subgroup.normalizer ((T.subgroupOf X : Subgroup X) : Set X) := by
    intro f
    rw [Subgroup.mem_normalizer_iff]
    intro y
    change (y : H) ∈ T ↔ ((xF f * y * (xF f)⁻¹ : X) : H) ∈ T
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hact f y y.2]
    exact Subgroup.mem_normalizer_iff.mp (hFT f.2) y
  have hFT' : η.range ≤ Subgroup.normalizer
      (((T.subgroupOf X).map π : Subgroup (X ⧸ Subgroup.center X)) : Set _) := by
    rintro _ ⟨f, rfl⟩
    exact Subgroup.le_normalizer_map π ⟨xF f, hxN f, rfl⟩
  have hTF' : ¬ (T.subgroupOf X).map π ≤ Subgroup.centralizer (η.range : Set _) := by
    intro hle
    apply hTF
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have htX : t ∈ X := hTX ht
    have h1 : π ⟨t, htX⟩ ∈ Subgroup.centralizer (η.range : Set _) := hle ⟨⟨t, htX⟩, ht, rfl⟩
    have h2 := Subgroup.mem_centralizer_iff.mp h1 (η ⟨f, hf⟩) ⟨⟨f, hf⟩, rfl⟩
    rw [hη] at h2
    have h3 : π ((xF ⟨f, hf⟩ * ⟨t, htX⟩)⁻¹ * (⟨t, htX⟩ * xF ⟨f, hf⟩)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, h2, inv_mul_cancel]
    rw [← MonoidHom.mem_ker, hker] at h3
    have hy : (f : H)⁻¹ * t * f ∈ X := by
      have h4 := (Subgroup.mem_normalizer_iff.mp (hFN (F.inv_mem hf)) t).mp htX
      rwa [inv_inv] at h4
    have hconj : ((xF ⟨f, hf⟩ : X) : H)⁻¹ * t * xF ⟨f, hf⟩ = (f : H)⁻¹ * t * f := by
      have h4 := hact ⟨f, hf⟩ _ hy
      have e : (f : H) * ((f : H)⁻¹ * t * f) * (f : H)⁻¹ = t := by group
      change (f : H) * ((f : H)⁻¹ * t * f) * (f : H)⁻¹ = _ at h4
      rw [e] at h4
      calc ((xF ⟨f, hf⟩ : X) : H)⁻¹ * t * xF ⟨f, hf⟩
          = ((xF ⟨f, hf⟩ : X) : H)⁻¹ * ((xF ⟨f, hf⟩ : H) * ((f : H)⁻¹ * t * f) *
              ((xF ⟨f, hf⟩ : X) : H)⁻¹) * xF ⟨f, hf⟩ := by rw [← h4]
        _ = (f : H)⁻¹ * t * f := by group
    have hwT : ((xF ⟨f, hf⟩ : H) * t)⁻¹ * (t * xF ⟨f, hf⟩) ∈ T := by
      have e : ((xF ⟨f, hf⟩ : H) * t)⁻¹ * (t * xF ⟨f, hf⟩) =
          t⁻¹ * (((xF ⟨f, hf⟩ : X) : H)⁻¹ * t * xF ⟨f, hf⟩) := by group
      rw [e, hconj]
      have h4 := (Subgroup.mem_normalizer_iff.mp (hFT (F.inv_mem hf)) t).mp ht
      rw [inv_inv] at h4
      exact T.mul_mem (T.inv_mem ht) h4
    have hw3 : (((xF ⟨f, hf⟩ : H) * t)⁻¹ * (t * xF ⟨f, hf⟩)) ^ 3 = 1 := by
      have h4 := hZ3' _ h3
      have h5 := congrArg Subtype.val h4
      simpa using h5
    have hw1 := Res413Cover.eq_one_of_isPGroup_two hT2 hwT hw3
    have hxt : (xF ⟨f, hf⟩ : H) * t = t * xF ⟨f, hf⟩ := (inv_mul_eq_one.mp hw1)
    have h5 := hact ⟨f, hf⟩ t htX
    change (f : H) * t * (f : H)⁻¹ = (xF ⟨f, hf⟩ : H) * t * (xF ⟨f, hf⟩ : H)⁻¹ at h5
    rw [hxt, mul_inv_cancel_right] at h5
    calc (f : H) * t = f * t * (f : H)⁻¹ * f := by group
      _ = t * f := by rw [h5]
  obtain ⟨r₁, r₂, g₁, g₂, hr12, hr13, hr23, hRcard, hRF, hFr, hgF, hgr1, hgr2, hg'r1, hg'r2⟩ :=
    hS (X ⧸ Subgroup.center X) hM η.range ((T.subgroupOf X).map π) hFe' hF9' hT2' hFT' hTF'
  obtain ⟨ρ₁, rfl⟩ := hsurj r₁
  obtain ⟨ρ₂, rfl⟩ := hsurj r₂
  obtain ⟨μ₁, rfl⟩ := hsurj g₁
  obtain ⟨μ₂, rfl⟩ := hsurj g₂
  have hρ12 : ρ₁ * ρ₂ = ρ₂ * ρ₁ := commute_of_sep π hkerZ hker3 hr12 hg'r1 hg'r2
  have hρ13 : ρ₁ ^ 3 = 1 := pow_three_eq_one_of_inv π hkerZ hker3 hr13 hgr1
  have hρ23 : ρ₂ ^ 3 = 1 := pow_three_eq_one_of_inv π hkerZ hker3 hr23 hgr2
  have hxρ1 : ∀ f : F, xF f * ρ₁ = ρ₁ * xF f := fun f =>
    commute_of_sep π hkerZ hker3 (hFr (η f) ⟨f, rfl⟩).1 (hgF (η f) ⟨f, rfl⟩) hgr1
  have hxρ2 : ∀ f : F, xF f * ρ₂ = ρ₂ * xF f := fun f =>
    commute_of_sep π hkerZ hker3 (hFr (η f) ⟨f, rfl⟩).2 (hgF (η f) ⟨f, rfl⟩) hgr2
  set R' : Subgroup X := Subgroup.closure ({ρ₁, ρ₂} : Set X) ⊔ Subgroup.center X with hR'
  have hZe : CFSG.Assembly.IsElemAbelian 3 (Subgroup.center X) :=
    ⟨⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 (a : X))⟩⟩, hZ3'⟩
  have hR'e : CFSG.Assembly.IsElemAbelian 3 R' := by
    refine isElemAbelian_sup_of_le_centralizer (isElemAbelian_closure_of_commute ?_ ?_) hZe ?_
    · rintro x (rfl | rfl) y (rfl | rfl)
      · exact Commute.refl _
      · exact hρ12
      · exact hρ12.symm
      · exact Commute.refl _
    · rintro x (rfl | rfl)
      · exact hρ13
      · exact hρ23
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact Subgroup.mem_center_iff.mp hz y
  have hR'map : R'.map π = Subgroup.closure ({π ρ₁, π ρ₂} : Set _) := by
    rw [hR', Subgroup.map_sup, MonoidHom.map_closure, Set.image_pair]
    have h1 : (Subgroup.center X).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hker]
    rw [h1, sup_bot_eq]
  have hR'card : Nat.card R' = 27 := by
    rw [Item434Alt.card_eq_card_inf_ker_mul_card_map π R', hR'map, hRcard, hker]
    have h1 : R' ⊓ Subgroup.center X = Subgroup.center X := inf_eq_right.mpr le_sup_right
    rw [h1, hZ3]
  have hcentF : ∀ x : X, (∀ f : F, xF f * x = x * xF f) →
      (x : H) ∈ Subgroup.centralizer (F : Set H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have h1 := hact ⟨f, hf⟩ x x.2
    have h2 : (xF ⟨f, hf⟩ : H) * x = x * xF ⟨f, hf⟩ := congrArg Subtype.val (hx ⟨f, hf⟩)
    change (f : H) * x * (f : H)⁻¹ = (xF ⟨f, hf⟩ : H) * x * (xF ⟨f, hf⟩ : H)⁻¹ at h1
    rw [h2, mul_inv_cancel_right] at h1
    calc (f : H) * x = f * x * (f : H)⁻¹ * f := by group
      _ = x * f := by rw [h1]
  have hFR : F ≤ Subgroup.centralizer ((R'.map X.subtype : Subgroup H) : Set H) := by
    rw [Subgroup.le_centralizer_iff, Subgroup.map_le_iff_le_comap]
    refine sup_le ?_ ?_
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hcentF _ hxρ1
      · exact hcentF _ hxρ2
    · intro z hz
      exact hcentF z fun f => (Subgroup.mem_center_iff.mp hz (xF f))
  let S : Subgroup H :=
    { carrier := {g | ∃ f ∈ F, ∀ y ∈ X, g * y * g⁻¹ = f * y * f⁻¹}
      mul_mem' := by
        rintro a b ⟨f₁, hf₁, ha⟩ ⟨f₂, hf₂, hb⟩
        refine ⟨f₁ * f₂, F.mul_mem hf₁ hf₂, fun y hy => ?_⟩
        have hy₂ : f₂ * y * f₂⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hFN hf₂) y).mp hy
        calc a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
          _ = a * (f₂ * y * f₂⁻¹) * a⁻¹ := by rw [hb y hy]
          _ = f₁ * (f₂ * y * f₂⁻¹) * f₁⁻¹ := ha _ hy₂
          _ = f₁ * f₂ * y * (f₁ * f₂)⁻¹ := by group
      one_mem' := ⟨1, F.one_mem, fun y _ => by group⟩
      inv_mem' := by
        rintro a ⟨f, hf, ha⟩
        refine ⟨f⁻¹, F.inv_mem hf, fun y hy => ?_⟩
        have hy' : f⁻¹ * y * f ∈ X := by
          have h4 := (Subgroup.mem_normalizer_iff.mp (hFN (F.inv_mem hf)) y).mp hy
          rwa [inv_inv] at h4
        calc a⁻¹ * y * a⁻¹⁻¹ = a⁻¹ * (f * (f⁻¹ * y * f) * f⁻¹) * a := by group
          _ = a⁻¹ * (a * (f⁻¹ * y * f) * a⁻¹) * a := by rw [ha _ hy']
          _ = f⁻¹ * y * f⁻¹⁻¹ := by group }
  have hFS : F ⊔ Subgroup.centralizer (X : Set H) ≤ S := by
    refine sup_le (fun f hf => ⟨f, hf, fun _ _ => rfl⟩) fun c hc => ⟨1, F.one_mem, fun y hy => ?_⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hc y hy
    calc c * y * c⁻¹ = y * c * c⁻¹ := by rw [h1]
      _ = 1 * y * 1⁻¹ := by group
  refine ⟨R'.map X.subtype, Subgroup.map_subtype_le R', isElemAbelian_map X.subtype hR'e, ?_,
    Subgroup.map_mono le_sup_right, hFR, ?_⟩
  · rw [Subgroup.card_map_of_injective X.subtype_injective, hR'card]
  · rintro r ⟨hrR, hrS'⟩
    obtain ⟨f, hf, hrf⟩ := hFS hrS'
    obtain ⟨ρ, hρR', rfl⟩ := hrR
    have h1 : π ρ = η ⟨f, hf⟩ :=
      hsame ρ (xF ⟨f, hf⟩) fun y hy => (hrf y hy).trans (hact ⟨f, hf⟩ y hy)
    have h2 : π ρ ∈ Subgroup.closure ({π ρ₁, π ρ₂} : Set _) := hR'map ▸ ⟨ρ, hρR', rfl⟩
    have h3 : π ρ ∈ Subgroup.closure ({π ρ₁, π ρ₂} : Set _) ⊓ η.range :=
      ⟨h2, h1 ▸ ⟨⟨f, hf⟩, rfl⟩⟩
    rw [hRF, Subgroup.mem_bot, ← MonoidHom.mem_ker, hker] at h3
    exact ⟨ρ, h3, rfl⟩

end Res417Five

end CFSG.RankThree.PartTwo.Sec4
