module

public import CFSG.Monster.Schur.GmatStructureExtraspecial
public import CFSG.Monster.Schur.Defs

public section

namespace CFSG.Monster.Schur

open Subgroup

variable {G E : Type*} [Group G] [Group E]

structure CentralKernel (π : E →* G) (n : E) : Prop where
  central : n ∈ Subgroup.center E
  mul_self : n * n = 1
  ne_one : n ≠ 1
  ker : π.ker = zpowers n

structure IsLiftComplement (π : E →* G) (n : E) (Q : Subgroup G) (S : Subgroup E) : Prop where
  le : S ≤ Q.comap π
  inf : S ⊓ zpowers n = ⊥
  sup : S ⊔ zpowers n = Q.comap π

theorem normal_zpowers_of_mem_center {n : E} (hn : n ∈ Subgroup.center E) :
    (zpowers n).Normal :=
  ⟨fun x hx g => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    have hc : Commute g n := (mem_center_iff.1 hn g)
    have : g * n ^ k * g⁻¹ = n ^ k := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (hc.zpow_right k).eq
    rw [this]
    exact hx⟩

theorem eq_one_or_eq_of_mem_zpowers_of_mul_self {n : E} (hn2 : n * n = 1) {w : E}
    (hw : w ∈ zpowers n) : w = 1 ∨ w = n := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
  have h2 : n ^ 2 = 1 := by rw [pow_two]; exact hn2
  have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h, add_zero, zpow_mul]
    simp [h2]
  · right
    rw [hk, h, zpow_add, zpow_mul]
    simp [h2]

namespace CentralKernel

variable {π : E →* G} {n : E} (hπ : CentralKernel π n)
include hπ

theorem eq_one_or_eq_of_mem_zpowers {w : E} (hw : w ∈ zpowers n) : w = 1 ∨ w = n :=
  eq_one_or_eq_of_mem_zpowers_of_mul_self hπ.mul_self hw

theorem eq_or_eq_mul_of_map_eq {a b : E} (h : π a = π b) : b = a ∨ b = a * n := by
  have hmem : a⁻¹ * b ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [hπ.ker] at hmem
  rcases hπ.eq_one_or_eq_of_mem_zpowers hmem with h1 | h1
  · left
    exact (inv_mul_eq_one.1 h1).symm
  · right
    rw [← h1, mul_inv_cancel_left]

theorem comm_n (e : E) : e * n = n * e := mem_center_iff.1 hπ.central e

theorem normal : (zpowers n).Normal := normal_zpowers_of_mem_center hπ.central

end CentralKernel

namespace IsLiftComplement

variable {π : E →* G} {n : E} {Q : Subgroup G} {S : Subgroup E}
  (hS : IsLiftComplement π n Q S) (hπ : CentralKernel π n)
include hS hπ

theorem unique {s s' : E} (hs : s ∈ S) (hs' : s' ∈ S) (e : π s = π s') : s = s' := by
  rcases hπ.eq_or_eq_mul_of_map_eq e with h | h
  · exact h.symm
  · have hn : n ∈ S := by
      have : s⁻¹ * s' ∈ S := S.mul_mem (S.inv_mem hs) hs'
      rw [h, inv_mul_cancel_left] at this
      exact this
    have : n ∈ S ⊓ zpowers n := ⟨hn, mem_zpowers n⟩
    rw [hS.inf] at this
    exact absurd (Subgroup.mem_bot.1 this) hπ.ne_one

theorem exists_lift {q : G} (hq : q ∈ Q) (hr : q ∈ π.range) : ∃ s ∈ S, π s = q := by
  obtain ⟨e, rfl⟩ := hr
  have he : e ∈ S ⊔ zpowers n := by rw [hS.sup]; exact hq
  have := hπ.normal
  obtain ⟨s, hs, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 he
  refine ⟨s, hs, ?_⟩
  have : π w = 1 := by
    rw [← MonoidHom.mem_ker, hπ.ker]
    exact hw
  rw [map_mul, this, mul_one]

end IsLiftComplement

section LemmaB

variable {π : E →* G} {n : E}

theorem lemmaB (hπ : CentralKernel π n) {Qx Qy Cx : Subgroup G} {Sx Sy : Subgroup E}
    (hSx : IsLiftComplement π n Qx Sx) (hSy : IsLiftComplement π n Qy Sy)
    (hQx : Qx ≤ π.range) (hQy : Qy ≤ π.range)
    (hnorm : ∀ c ∈ Cx.comap π, ∀ s ∈ Sx, c * s * c⁻¹ ∈ Sx)
    {u v y : G} (hu : u ∈ Qx ⊓ Qy) (hv : v ∈ Qy ⊓ Cx) (huv : u * v * u⁻¹ * v⁻¹ = y)
    {ζ : E} (hζ : ζ ∈ Sy) (hζy : π ζ = y) : ζ ∈ Sx := by
  obtain ⟨uX, huX, huXu⟩ := hSx.exists_lift hπ hu.1 (hQx hu.1)
  obtain ⟨uY, huY, huYu⟩ := hSy.exists_lift hπ hu.2 (hQy hu.2)
  obtain ⟨vY, hvY, hvYv⟩ := hSy.exists_lift hπ hv.1 (hQy hv.1)
  have hcomm : uX * vY * uX⁻¹ * vY⁻¹ = uY * vY * uY⁻¹ * vY⁻¹ := by
    rcases hπ.eq_or_eq_mul_of_map_eq (huYu.trans huXu.symm) with h | h
    · rw [h]
    · have hnv : n * vY = vY * n := (hπ.comm_n vY).symm
      rw [h]
      calc (uY * n) * vY * (uY * n)⁻¹ * vY⁻¹ = uY * (n * vY) * n⁻¹ * uY⁻¹ * vY⁻¹ := by group
        _ = uY * (vY * n) * n⁻¹ * uY⁻¹ * vY⁻¹ := by rw [hnv]
        _ = uY * vY * uY⁻¹ * vY⁻¹ := by group
  have hSyc : uY * vY * uY⁻¹ * vY⁻¹ ∈ Sy :=
    Sy.mul_mem (Sy.mul_mem (Sy.mul_mem huY hvY) (Sy.inv_mem huY)) (Sy.inv_mem hvY)
  have hπc : π (uY * vY * uY⁻¹ * vY⁻¹) = π ζ := by
    rw [hζy, map_mul, map_mul, map_mul, map_inv, map_inv, huYu, hvYv, huv]
  have hζeq : uY * vY * uY⁻¹ * vY⁻¹ = ζ := hSy.unique hπ hSyc hζ hπc
  have hvYC : vY ∈ Cx.comap π := by
    rw [Subgroup.mem_comap, hvYv]
    exact hv.2
  have hSx' : uX * (vY * uX⁻¹ * vY⁻¹) ∈ Sx := Sx.mul_mem huX (hnorm vY hvYC _ (Sx.inv_mem huX))
  rw [← hζeq, ← hcomm]
  simpa only [mul_assoc] using hSx'

end LemmaB

section LemmaC

variable {π : E →* G} {n : E}

theorem lemmaC {Qx Qy Cx Cy : Subgroup G} {x y : G} {Sx Sy : Subgroup E} [Finite Qy]
    (hπ : CentralKernel π n)
    (hSx : IsLiftComplement π n Qx Sx) (hSy : IsLiftComplement π n Qy Sy)
    (hQx : Qx ≤ π.range) (hQy : Qy ≤ π.range) (hCV : Cx ⊓ Cy ≤ π.range)
    (hnx : ∀ c ∈ Cx.comap π, ∀ s ∈ Sx, c * s * c⁻¹ ∈ Sx)
    (hny : ∀ c ∈ Cy.comap π, ∀ s ∈ Sy, c * s * c⁻¹ ∈ Sy)
    (hnQx : ∀ g ∈ Cx, ∀ a ∈ Qx, g * a * g⁻¹ ∈ Qx)
    (hnQy : ∀ g ∈ Cy, ∀ a ∈ Qy, g * a * g⁻¹ ∈ Qy)
    (hQyext : IsExtraspecialAmbient Qy y)
    (hZab : ∀ a ∈ Qx ⊓ Qy, ∀ b ∈ Qx ⊓ Qy, a * b = b * a)
    (hZlow : 2 * Nat.card Qy ≤ Nat.card ↥(Qx ⊓ Qy) * Nat.card ↥(Qx ⊓ Qy))
    (hxΛ : ∃ s ∈ Sx ⊓ Sy, π s = x) (hyΛ : ∃ s ∈ Sx ⊓ Sy, π s = y)
    (hxCx : ∀ g ∈ Qy, g * x = x * g → g ∈ Cx)
    (hW3 : ∀ r ∈ Qy ⊓ Cx, (∀ g ∈ Cx ⊓ Cy, r⁻¹ * (g * r * g⁻¹) ∈ Qx) → r ∈ Qx) :
    ∀ s ∈ Sx, π s ∈ Qy → s ∈ Sy := by
  classical
  set Z : Subgroup G := Qx ⊓ Qy with hZdef
  set Λ : Subgroup G := (Sx ⊓ Sy).map π with hΛdef
  have hmemΛ : ∀ u, u ∈ Λ ↔ ∃ s ∈ Sx ⊓ Sy, π s = u := fun u => Subgroup.mem_map
  have hΛZ : Λ ≤ Z := by
    intro u hu
    obtain ⟨s, ⟨hsx, hsy⟩, rfl⟩ := (hmemΛ u).1 hu
    exact ⟨hSx.le hsx, hSy.le hsy⟩
  have hxΛ' : x ∈ Λ := (hmemΛ x).2 hxΛ
  have hyΛ' : y ∈ Λ := (hmemΛ y).2 hyΛ
  have hΛnorm : ∀ g ∈ Cx ⊓ Cy, ∀ a ∈ Λ, g * a * g⁻¹ ∈ Λ := by
    intro g hg a ha
    obtain ⟨s, ⟨hsx, hsy⟩, rfl⟩ := (hmemΛ a).1 ha
    obtain ⟨c, rfl⟩ := hCV hg
    refine (hmemΛ _).2 ⟨c * s * c⁻¹, ⟨hnx c hg.1 s hsx, hny c hg.2 s hsy⟩, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hZnorm : ∀ g ∈ Cx ⊓ Cy, ∀ a ∈ Z, g * a * g⁻¹ ∈ Z := fun g hg a ha =>
    ⟨hnQx g hg.1 a ha.1, hnQy g hg.2 a ha.2⟩
  have hZQy : Z ≤ Qy := inf_le_right
  have hc1 : ∀ u₀ ∈ Z, u₀ ∉ Λ → ∀ u ∈ Z, u ∉ Λ → u₀⁻¹ * u ∈ Λ := by
    intro u₀ hu₀ hu₀Λ u hu huΛ
    obtain ⟨a, ha, haπ⟩ := hSx.exists_lift hπ hu₀.1 (hQx hu₀.1)
    obtain ⟨a', ha', ha'π⟩ := hSy.exists_lift hπ hu₀.2 (hQy hu₀.2)
    obtain ⟨b, hb, hbπ⟩ := hSx.exists_lift hπ hu.1 (hQx hu.1)
    obtain ⟨b', hb', hb'π⟩ := hSy.exists_lift hπ hu.2 (hQy hu.2)
    have hA : a' = a * n := by
      rcases hπ.eq_or_eq_mul_of_map_eq (haπ.trans ha'π.symm) with h | h
      · exact absurd ((hmemΛ u₀).2 ⟨a, ⟨ha, h ▸ ha'⟩, haπ⟩) hu₀Λ
      · exact h
    have hB : b' = b * n := by
      rcases hπ.eq_or_eq_mul_of_map_eq (hbπ.trans hb'π.symm) with h | h
      · exact absurd ((hmemΛ u).2 ⟨b, ⟨hb, h ▸ hb'⟩, hbπ⟩) huΛ
      · exact h
    have hab : (a * n)⁻¹ * (b * n) = a⁻¹ * b := by
      calc (a * n)⁻¹ * (b * n) = n⁻¹ * ((a⁻¹ * b) * n) := by group
        _ = n⁻¹ * (n * (a⁻¹ * b)) := by rw [hπ.comm_n]
        _ = a⁻¹ * b := by group
    refine (hmemΛ _).2 ⟨a⁻¹ * b, ⟨Sx.mul_mem (Sx.inv_mem ha) hb, ?_⟩, ?_⟩
    · rw [← hab, ← hA, ← hB]
      exact Sy.mul_mem (Sy.inv_mem ha') hb'
    · rw [map_mul, map_inv, haπ, hbπ]
  have hCZ : Qy ⊓ centralizer (Z : Set G) ≤ Z := by
    have hyZ : y ∈ Z := hΛZ hyΛ'
    have h1 := hQyext.card_inf_centralizer_mul_card (A := Z) hZQy hyZ
    have hZfin : Finite Z := Finite.of_injective (Subgroup.inclusion hZQy)
      (Subgroup.inclusion_injective hZQy)
    have hCfin : Finite ↥(Qy ⊓ centralizer (Z : Set G)) :=
      Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
    have hpos : 0 < Nat.card Z := Nat.card_pos
    have hle : Nat.card ↥(Qy ⊓ centralizer (Z : Set G)) ≤ Nat.card Z := by
      by_contra hlt
      push Not at hlt
      have := Nat.mul_lt_mul_of_lt_of_le hlt (le_refl (Nat.card Z)) hpos
      omega
    have hZC : Z ≤ Qy ⊓ centralizer (Z : Set G) := fun a ha =>
      ⟨hZQy ha, Subgroup.mem_centralizer_iff.2 fun b hb => hZab b hb a ha⟩
    exact (Subgroup.eq_of_le_of_card_ge hZC hle).symm.le
  have hZle : Z ≤ Λ := by
    by_contra hnle
    obtain ⟨u₀, hu₀Z, hu₀Λ⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
    have hlt : Λ < Z := lt_of_le_of_ne hΛZ fun h => hu₀Λ (h ▸ hu₀Z)
    obtain ⟨r, hrQy, hrΛ, a₀, ha₀Z, ha₀r⟩ :=
      hQyext.exists_mem_centralizer_not_mem_of_lt (A₁ := Λ) (A₂ := Z) hZQy hyΛ' hlt
    have hZcomm : ∀ t : G, (∀ a ∈ Λ, a * t = t * a) → u₀ * t = t * u₀ →
        ∀ a ∈ Z, a * t = t * a := by
      intro t htΛ htu a ha
      by_cases haΛ : a ∈ Λ
      · exact htΛ a haΛ
      · have h1 := hc1 u₀ hu₀Z hu₀Λ a ha haΛ
        have h2 := htΛ _ h1
        calc a * t = u₀ * ((u₀⁻¹ * a) * t) := by group
          _ = u₀ * (t * (u₀⁻¹ * a)) := by rw [h2]
          _ = (u₀ * t) * (u₀⁻¹ * a) := by group
          _ = (t * u₀) * (u₀⁻¹ * a) := by rw [htu]
          _ = t * a := by group
    have hru : u₀ * r ≠ r * u₀ := fun h => ha₀r (hZcomm r hrΛ h a₀ ha₀Z)
    have hkey : ∀ g ∈ Cx ⊓ Cy, r⁻¹ * (g * r * g⁻¹) ∈ Qx := by
      intro g hg
      have hg' : g⁻¹ ∈ Cx ⊓ Cy := inv_mem hg
      have hr'Qy : g * r * g⁻¹ ∈ Qy := hnQy g hg.2 r hrQy
      have hr'Λ : ∀ a ∈ Λ, a * (g * r * g⁻¹) = (g * r * g⁻¹) * a := by
        intro a ha
        have h1 := hrΛ _ (hΛnorm g⁻¹ hg' a ha)
        simp only [inv_inv] at h1
        calc a * (g * r * g⁻¹) = g * ((g⁻¹ * a * g) * r) * g⁻¹ := by group
          _ = g * (r * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
          _ = (g * r * g⁻¹) * a := by group
      have hr'u : u₀ * (g * r * g⁻¹) ≠ (g * r * g⁻¹) * u₀ := by
        intro h
        apply ha₀r
        have hc := hZcomm _ hr'Λ h (g * a₀ * g⁻¹) (hZnorm g hg a₀ ha₀Z)
        calc a₀ * r = g⁻¹ * ((g * a₀ * g⁻¹) * (g * r * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * r * g⁻¹) * (g * a₀ * g⁻¹)) * g := by rw [hc]
          _ = r * a₀ := by group
      have hwu : u₀ * (r⁻¹ * (g * r * g⁻¹)) = (r⁻¹ * (g * r * g⁻¹)) * u₀ :=
        hQyext.commute_inv_mul_of_not_commute (hZQy hu₀Z) hrQy hr'Qy hru hr'u
      have hwΛ : ∀ a ∈ Λ, a * (r⁻¹ * (g * r * g⁻¹)) = (r⁻¹ * (g * r * g⁻¹)) * a := by
        intro a ha
        exact ((Commute.inv_right (hrΛ a ha)).mul_right (hr'Λ a ha)).eq
      have hwZ := hZcomm _ hwΛ hwu
      have hwQy : r⁻¹ * (g * r * g⁻¹) ∈ Qy := Qy.mul_mem (Qy.inv_mem hrQy) hr'Qy
      have hwC : r⁻¹ * (g * r * g⁻¹) ∈ Qy ⊓ centralizer (Z : Set G) :=
        ⟨hwQy, Subgroup.mem_centralizer_iff.2 hwZ⟩
      exact (hCZ hwC).1
    have hrCx : r ∈ Cx := hxCx r hrQy (hrΛ x hxΛ').symm
    have hrQx : r ∈ Qx := hW3 r ⟨hrQy, hrCx⟩ hkey
    exact ha₀r (hZab a₀ ha₀Z r ⟨hrQx, hrQy⟩)
  intro s hs hsQ
  obtain ⟨s', ⟨hs'x, hs'y⟩, hs'π⟩ := (hmemΛ (π s)).1 (hZle ⟨hSx.le hs, hsQ⟩)
  rw [← hSx.unique hπ hs hs'x hs'π.symm] at hs'y
  exact hs'y

end LemmaC

section Conj

variable {π : E →* G} {n : E}

theorem conjSub_zpowers_eq {t : E} (hn : n ∈ Subgroup.center E) :
    conjSub t (zpowers n) = zpowers n := by
  rw [conjSub, MonoidHom.map_zpowers]
  congr 1
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [mul_inv_eq_iff_eq_mul]
  exact (mem_center_iff.1 hn t)

theorem conjSub_comap (t : E) (Q : Subgroup G) :
    conjSub t (Q.comap π) = (conjSub (π t) Q).comap π := by
  ext e
  rw [mem_conjSub, Subgroup.mem_comap, Subgroup.mem_comap, mem_conjSub, map_mul, map_mul,
    map_inv]

theorem IsLiftComplement.conj (hπ : CentralKernel π n) {Q : Subgroup G} {S : Subgroup E}
    (hS : IsLiftComplement π n Q S) (t : E) :
    IsLiftComplement π n (conjSub (π t) Q) (conjSub t S) := by
  have hz := conjSub_zpowers_eq (t := t) hπ.central
  have hsup : conjSub t S ⊔ zpowers n = (conjSub (π t) Q).comap π := by
    rw [← conjSub_comap, ← hS.sup, conjSub, conjSub, Subgroup.map_sup]
    congr 1
    exact hz.symm
  refine ⟨?_, ?_, hsup⟩
  · rw [← hsup]
    exact le_sup_left
  · have hinj : Function.Injective (MulAut.conj t).toMonoidHom := (MulAut.conj t).injective
    have h1 := Subgroup.map_inf S (zpowers n) (MulAut.conj t).toMonoidHom hinj
    rw [hS.inf, Subgroup.map_bot] at h1
    have hz' : (zpowers n).map (MulAut.conj t).toMonoidHom = zpowers n := hz
    calc conjSub t S ⊓ zpowers n
        = S.map (MulAut.conj t).toMonoidHom ⊓ (zpowers n).map (MulAut.conj t).toMonoidHom := by
          rw [hz']; rfl
      _ = ⊥ := h1.symm

theorem conj_normalizes {Cx : Subgroup G} {S : Subgroup E}
    (hn : ∀ c ∈ Cx.comap π, ∀ s ∈ S, c * s * c⁻¹ ∈ S) (t : E) :
    ∀ c ∈ (conjSub (π t) Cx).comap π, ∀ s ∈ conjSub t S, c * s * c⁻¹ ∈ conjSub t S := by
  intro c hc s hs
  rw [Subgroup.mem_comap, mem_conjSub, ← map_inv, ← map_mul, ← map_mul] at hc
  rw [mem_conjSub] at hs ⊢
  have := hn _ hc _ hs
  convert this using 1
  group

end Conj

section Split

theorem exists_complement_of_noPerfectDoubleCover {X A : Type} [Group X] [Group A]
    (hAp : Group.IsPerfect A) (hND : NoPerfectDoubleCover A) (ψ : X →* A)
    (hψ : Function.Surjective ψ) {n : X} (hn : n ∈ Subgroup.center X) (hn2 : n * n = 1)
    (hn1 : n ≠ 1) (K : Subgroup X) [K.Normal] (hKn : K ⊓ zpowers n = ⊥)
    (hker : ψ.ker = K ⊔ zpowers n) :
    ∃ D : Subgroup X, D ⊓ zpowers n = ⊥ ∧ D ⊔ zpowers n = ⊤ := by
  have hnorm : (zpowers n).Normal := normal_zpowers_of_mem_center hn
  have hKle : K ≤ ψ.ker := by rw [hker]; exact le_sup_left
  have hnker : n ∈ ψ.ker := by rw [hker]; exact Subgroup.mem_sup_right (mem_zpowers n)
  let ψb : X ⧸ K →* A := QuotientGroup.lift K ψ hKle
  have hψb : Function.Surjective ψb := by
    intro a
    obtain ⟨x, rfl⟩ := hψ a
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hnK : n ∉ K := fun h => hn1 (by
    have : n ∈ K ⊓ zpowers n := ⟨h, mem_zpowers n⟩
    rwa [hKn, Subgroup.mem_bot] at this)
  have hmk1 : (QuotientGroup.mk n : X ⧸ K) ≠ 1 := fun h => hnK ((QuotientGroup.eq_one_iff n).1 h)
  have hmk2 : (QuotientGroup.mk n : X ⧸ K) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, pow_two, hn2]
    rfl
  have hkerb : ψb.ker = zpowers (QuotientGroup.mk n : X ⧸ K) := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidHom.mem_ker, mem_zpowers_iff]
    constructor
    · intro hx
      have hxk : x ∈ ψ.ker := hx
      rw [hker] at hxk
      obtain ⟨k, hk, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hxk
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
      refine ⟨j, ?_⟩
      rw [← QuotientGroup.mk_zpow, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff k).2 hk,
        one_mul]
    · rintro ⟨j, hj⟩
      have : ψb (QuotientGroup.mk (n ^ j)) = 1 := by
        show ψ (n ^ j) = 1
        rw [map_zpow, MonoidHom.mem_ker.1 hnker, one_zpow]
      rw [← hj, ← QuotientGroup.mk_zpow]
      exact this
  have hcard : Nat.card ψb.ker = 2 := by
    rw [hkerb, Nat.card_zpowers]
    exact orderOf_eq_prime hmk2 hmk1
  set D : Subgroup X := commutator X ⊔ K with hD
  have hDtop : D ≠ ⊤ := by
    intro hDtop
    refine hND (X ⧸ K) ψb hψb ⟨?_⟩ hcard
    have h1 : (commutator X).map (QuotientGroup.mk' K) = commutator (X ⧸ K) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)]
    have h2 : D.map (QuotientGroup.mk' K) = ⊤ := by
      rw [hDtop]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)
    rw [hD, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq, h1] at h2
    exact h2
  have hDsup : D ⊔ zpowers n = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have hcomm : (commutator X).map ψ = ⊤ := by
      rw [_root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ hψ, ← _root_.commutator_def]
      exact hAp.commutator_eq_top
    have hx : ψ x ∈ (commutator X).map ψ := by rw [hcomm]; trivial
    obtain ⟨d, hd, hdx⟩ := hx
    have hmem : d⁻¹ * x ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdx, inv_mul_cancel]
    rw [hker] at hmem
    obtain ⟨k, hk, w, hw, hkw⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
    have hxe : x = (d * k) * w := by rw [mul_assoc, hkw]; group
    rw [hxe]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mul_mem _ (Subgroup.mem_sup_left hd)
        (Subgroup.mem_sup_right hk)))
      (Subgroup.mem_sup_right hw)
  refine ⟨D, ?_, hDsup⟩
  rw [eq_bot_iff]
  rintro w ⟨hwD, hwn⟩
  rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hn2 hwn with h | h
  · rw [h]
    exact one_mem _
  · exfalso
    rw [h] at hwD
    apply hDtop
    rw [← hDsup]
    exact (sup_eq_left.2 (zpowers_le.2 hwD)).symm

theorem exists_complement_in_subgroup {E A : Type} [Group E] [Group A]
    (hAp : Group.IsPerfect A) (hND : NoPerfectDoubleCover A) {H : Subgroup E} (ψ : H →* A)
    (hψ : Function.Surjective ψ) {n : E} (hnH : n ∈ H) (hn : n ∈ Subgroup.center E)
    (hn2 : n * n = 1) (hn1 : n ≠ 1) {K : Subgroup E} (hKH : K ≤ H)
    (hKnorm : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) (hKn : K ⊓ zpowers n = ⊥)
    (hker : ψ.ker = (K ⊔ zpowers n).subgroupOf H) :
    ∃ D : Subgroup E, D ≤ H ∧ D ⊓ zpowers n = ⊥ ∧ D ⊔ zpowers n = H := by
  have hKN : (K.subgroupOf H).Normal :=
    ⟨fun x hx g => Subgroup.mem_subgroupOf.2 (hKnorm g.1 g.2 x (Subgroup.mem_subgroupOf.1 hx))⟩
  let n' : H := ⟨n, hnH⟩
  have hn' : n' ∈ Subgroup.center H :=
    mem_center_iff.2 fun g => Subtype.ext (mem_center_iff.1 hn g)
  have hz : (zpowers n).subgroupOf H = zpowers n' := by
    ext g
    rw [Subgroup.mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hker' : ψ.ker = K.subgroupOf H ⊔ zpowers n' := by
    rw [hker, Subgroup.subgroupOf_sup hKH (zpowers_le.2 hnH), hz]
  have hKn' : K.subgroupOf H ⊓ zpowers n' = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hg1, hg2⟩
    have h1 : (g : E) ∈ K := Subgroup.mem_subgroupOf.1 hg1
    have h2 : (g : E) ∈ zpowers n := by
      rw [← hz] at hg2
      exact Subgroup.mem_subgroupOf.1 hg2
    have : (g : E) ∈ K ⊓ zpowers n := ⟨h1, h2⟩
    rw [hKn, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  obtain ⟨D', hD'inf, hD'sup⟩ := exists_complement_of_noPerfectDoubleCover hAp hND ψ hψ hn'
    (Subtype.ext hn2) (fun h => hn1 (congrArg Subtype.val h)) (K.subgroupOf H) hKn' hker'
  have hinj : Function.Injective H.subtype := Subtype.val_injective
  have hzn : (zpowers n').map H.subtype = zpowers n := by
    rw [MonoidHom.map_zpowers]
    rfl
  refine ⟨D'.map H.subtype, Subgroup.map_subtype_le D', ?_, ?_⟩
  · rw [← hzn, ← Subgroup.map_inf _ _ _ hinj, hD'inf, Subgroup.map_bot]
  · rw [← hzn, ← Subgroup.map_sup, hD'sup, Subgroup.map_top, Subgroup.range_subtype]

end Split

theorem exists_mul_of_mem_sup {A B : Subgroup G} (hB : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A)
    {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, B.one_mem, (mul_one x).symm⟩
    · exact ⟨1, A.one_mem, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, (one_mul 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hy
    exact ⟨a * (b * a' * b⁻¹), A.mul_mem ha (hB b hb a' ha'), b * b', B.mul_mem hb hb',
      by group⟩
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact ⟨b⁻¹ * a⁻¹ * b⁻¹⁻¹, by simpa using hB b⁻¹ (B.inv_mem hb) a⁻¹ (A.inv_mem ha), b⁻¹,
      B.inv_mem hb, by group⟩

section Step4

variable {F : Type} [Group F] {π : F →* G} {n : F}

theorem exists_complement_over {Qx Qy Cx Cy P R : Subgroup G} {Sx Sy : Subgroup F}
    (hπ : CentralKernel π n)
    (hSx : IsLiftComplement π n Qx Sx) (hSy : IsLiftComplement π n Qy Sy)
    (hQx : Qx ≤ π.range) (hQy : Qy ≤ π.range) (hCV : Cx ⊓ Cy ≤ π.range)
    (hnx : ∀ c ∈ Cx.comap π, ∀ s ∈ Sx, c * s * c⁻¹ ∈ Sx)
    (hny : ∀ c ∈ Cy.comap π, ∀ s ∈ Sy, c * s * c⁻¹ ∈ Sy)
    (hnQx : ∀ g ∈ Cx, ∀ a ∈ Qx, g * a * g⁻¹ ∈ Qx)
    (hnQy : ∀ g ∈ Cy, ∀ a ∈ Qy, g * a * g⁻¹ ∈ Qy)
    (hQyCy : Qy ≤ Cy)
    (hC : ∀ s ∈ Sx, π s ∈ Qy → s ∈ Sy)
    (hPdef : P = Qx ⊔ (Cx ⊓ Cy)) (hRdef : R = Qy ⊓ Cx)
    {A : Type} [Group A] (hAp : Group.IsPerfect A) (hND : NoPerfectDoubleCover A)
    (ψ : ↥P →* A) (hψ : Function.Surjective ψ)
    (hψker : ψ.ker = (Qx ⊔ R).subgroupOf P) (hP : P ≤ π.range) :
    ∃ D : Subgroup F, D ≤ P.comap π ∧ D ⊓ zpowers n = ⊥ ∧ D ⊔ zpowers n = P.comap π := by
  classical
  set Ry : Subgroup F := Sy ⊓ R.comap π with hRydef
  set K1 : Subgroup F := Sx ⊔ Ry with hK1def
  have hcentral : ∀ w ∈ zpowers n, ∀ e : F, e * w = w * e := fun w hw e =>
    mem_center_iff.1 (zpowers_le.2 hπ.central hw) e
  have hπn : π n = 1 := MonoidHom.mem_ker.1 (by rw [hπ.ker]; exact mem_zpowers n)
  have hQxP : Qx ≤ P := hPdef ▸ le_sup_left
  have hRCx : R ≤ Cx := hRdef ▸ inf_le_right
  have hRQy : R ≤ Qy := hRdef ▸ inf_le_left
  have hRCV : R ≤ Cx ⊓ Cy := fun r hr => ⟨hRCx hr, hQyCy (hRQy hr)⟩
  have hRP : R ≤ P := hRCV.trans (hPdef ▸ le_sup_right)
  have hRyN : ∀ b ∈ Ry, ∀ s ∈ Sx, b * s * b⁻¹ ∈ Sx := fun b hb s hs => hnx b (hRCx hb.2) s hs
  have hK1mem : ∀ k ∈ K1, ∃ s ∈ Sx, ∃ b ∈ Ry, k = s * b := fun k hk =>
    exists_mul_of_mem_sup hRyN hk
  have hK1H : K1 ≤ P.comap π := by
    refine sup_le (fun s hs => ?_) (fun b hb => ?_)
    · exact hQxP (hSx.le hs)
    · exact hRP hb.2
  have hnormQ : ∀ a ∈ Qx.comap π, ∀ k ∈ K1, a * k * a⁻¹ ∈ K1 := by
    intro a ha k hk
    rw [← hSx.sup] at ha
    obtain ⟨s, hs, w, hw, rfl⟩ := exists_mul_of_mem_sup (A := Sx) (B := zpowers n)
      (fun b hb a' ha' => by
        have : b * a' * b⁻¹ = a' := by
          rw [mul_inv_eq_iff_eq_mul]
          exact (hcentral b hb a').symm
        rw [this]
        exact ha') ha
    have e1 : s * w * k * (s * w)⁻¹ = s * k * s⁻¹ := by
      have hwk : w * k = k * w := (hcentral w hw k).symm
      calc s * w * k * (s * w)⁻¹ = s * (w * k) * w⁻¹ * s⁻¹ := by group
        _ = s * (k * w) * w⁻¹ * s⁻¹ := by rw [hwk]
        _ = s * k * s⁻¹ := by group
    rw [e1]
    exact K1.mul_mem (K1.mul_mem (Subgroup.mem_sup_left hs) hk)
      (K1.inv_mem (Subgroup.mem_sup_left hs))
  have hnormC : ∀ c ∈ (Cx ⊓ Cy).comap π, ∀ k ∈ K1, c * k * c⁻¹ ∈ K1 := by
    intro c hc k hk
    obtain ⟨s, hs, b, hb, rfl⟩ := hK1mem k hk
    have e : c * (s * b) * c⁻¹ = (c * s * c⁻¹) * (c * b * c⁻¹) := by group
    rw [e]
    refine K1.mul_mem (Subgroup.mem_sup_left (hnx c hc.1 s hs))
      (Subgroup.mem_sup_right ⟨hny c hc.2 b hb.1, ?_⟩)
    show π (c * b * c⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv, hRdef]
    have hbR : π b ∈ Qy ⊓ Cx := hRdef ▸ hb.2
    exact ⟨hnQy _ hc.2 _ hbR.1, Cx.mul_mem (Cx.mul_mem hc.1 hbR.2) (Cx.inv_mem hc.1)⟩
  have hnormK1 : ∀ h ∈ P.comap π, ∀ k ∈ K1, h * k * h⁻¹ ∈ K1 := by
    intro h hh k hk
    have hh' : π h ∈ Qx ⊔ (Cx ⊓ Cy) := hPdef ▸ hh
    obtain ⟨q, hq, c', hc', hqc⟩ := exists_mul_of_mem_sup (A := Qx) (B := Cx ⊓ Cy)
      (fun g hg a ha => hnQx g hg.1 a ha) hh'
    obtain ⟨c, hcπ⟩ := hCV hc'
    have hcC : c ∈ (Cx ⊓ Cy).comap π := by
      show π c ∈ Cx ⊓ Cy
      rw [hcπ]
      exact hc'
    have haQ : h * c⁻¹ ∈ Qx.comap π := by
      show π (h * c⁻¹) ∈ Qx
      rw [map_mul, map_inv, hcπ, hqc, mul_inv_cancel_right]
      exact hq
    have e : h * k * h⁻¹ = (h * c⁻¹) * (c * k * c⁻¹) * (h * c⁻¹)⁻¹ := by group
    rw [e]
    exact hnormQ _ haQ _ (hnormC c hcC k hk)
  have hK1n : K1 ⊓ zpowers n = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwK, hwn⟩
    rcases hπ.eq_one_or_eq_of_mem_zpowers hwn with h | h
    · rw [h]
      exact one_mem _
    · exfalso
      rw [h] at hwK
      obtain ⟨s, hs, b, hb, hsb⟩ := hK1mem n hwK
      have hπb : π b = π s⁻¹ := by
        have h1 : π s * π b = 1 := by rw [← map_mul, ← hsb, hπn]
        rw [map_inv]
        exact eq_inv_of_mul_eq_one_right h1
      have hbQy : π s⁻¹ ∈ Qy := hπb ▸ hRQy hb.2
      have h2 : s⁻¹ ∈ Sy := hC _ (Sx.inv_mem hs) hbQy
      have h3 : b = s⁻¹ := hSy.unique hπ hb.1 h2 hπb
      apply hπ.ne_one
      rw [hsb, h3, mul_inv_cancel]
  have hker : ∀ h : F, π h ∈ Qx ⊔ R ↔ h ∈ K1 ⊔ zpowers n := by
    intro h
    constructor
    · intro hmem
      obtain ⟨q, hq, r, hr, hqr⟩ := exists_mul_of_mem_sup (A := Qx) (B := R)
        (fun g hg a ha => hnQx g (hRCx hg) a ha) hmem
      obtain ⟨qX, hqX, hqXπ⟩ := hSx.exists_lift hπ hq (hQx hq)
      obtain ⟨rY, hrY, hrYπ⟩ := hSy.exists_lift hπ (hRQy hr) (hQy (hRQy hr))
      have hrR : rY ∈ Ry := ⟨hrY, by show π rY ∈ R; rw [hrYπ]; exact hr⟩
      have hmul : π (qX * rY) = π h := by rw [map_mul, hqXπ, hrYπ, hqr]
      have hK : qX * rY ∈ K1 :=
        K1.mul_mem (Subgroup.mem_sup_left hqX) (Subgroup.mem_sup_right hrR)
      rcases hπ.eq_or_eq_mul_of_map_eq hmul with h1 | h1
      · rw [h1]
        exact Subgroup.mem_sup_left hK
      · rw [h1]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hK)
          (Subgroup.mem_sup_right (mem_zpowers n))
    · intro hmem
      have hle : K1 ⊔ zpowers n ≤ (Qx ⊔ R).comap π := by
        refine sup_le (sup_le (fun s hs => ?_) (fun b hb => ?_)) (fun w hw => ?_)
        · exact Subgroup.mem_sup_left (hSx.le hs)
        · exact Subgroup.mem_sup_right hb.2
        · have : π w = 1 := MonoidHom.mem_ker.1 (by rw [hπ.ker]; exact hw)
          show π w ∈ Qx ⊔ R
          rw [this]
          exact one_mem _
      exact hle hmem
  let πH : (P.comap π) →* P := π.subgroupComap P
  let ψH : (P.comap π) →* A := ψ.comp πH
  have hπH : Function.Surjective πH := by
    intro g
    obtain ⟨e, he⟩ := hP g.2
    exact ⟨⟨e, by show π e ∈ P; rw [he]; exact g.2⟩, Subtype.ext he⟩
  have hψH : Function.Surjective ψH := hψ.comp hπH
  have hnH : n ∈ P.comap π := by
    show π n ∈ P
    rw [hπn]
    exact one_mem _
  have hψHker : ψH.ker = (K1 ⊔ zpowers n).subgroupOf (P.comap π) := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change ψ (πH h) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hψker, Subgroup.mem_subgroupOf]
    exact hker h.1
  exact exists_complement_in_subgroup hAp hND ψH hψH hnH hπ.central hπ.mul_self hπ.ne_one hK1H
    hnormK1 hK1n hψHker

end Step4

end CFSG.Monster.Schur
