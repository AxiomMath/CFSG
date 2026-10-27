module

public import CFSG.RankThree.PartOne.K1320.L4Transport
public import CFSG.RankThree.PartOne.S12.Equivariance
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG.RankThree.PartOne

variable {G : Type} [Group G] {L : Subgroup G} {M P : Type} [Group M] [Group P]

@[expose] def liftM (ε : ↥L →* P) (ψ : M →* P) (S : Subgroup M) : Subgroup G :=
  pullG ε (S.map ψ)

section
variable {ε : ↥L →* P} {ψ : M →* P}

theorem liftM_le (S : Subgroup M) : liftM ε ψ S ≤ L := pullG_le ε _

theorem mem_liftM {S : Subgroup M} {x : G} :
    x ∈ liftM ε ψ S ↔ ∃ hx : x ∈ L, ∃ s ∈ S, ψ s = ε ⟨x, hx⟩ := by
  unfold liftM
  rw [mem_pullG]
  refine exists_congr fun hx => ?_
  rw [Subgroup.mem_map]

theorem liftM_mono {S T : Subgroup M} (h : S ≤ T) : liftM ε ψ S ≤ liftM ε ψ T :=
  pullG_mono ε (Subgroup.map_mono h)

theorem liftM_inf (hψ : Function.Injective ψ) (S T : Subgroup M) :
    liftM ε ψ (S ⊓ T) = liftM ε ψ S ⊓ liftM ε ψ T := by
  unfold liftM
  rw [Subgroup.map_inf _ _ _ hψ, pullG_inf]

theorem liftM_sup (hs : Function.Surjective ε) (hi : Function.Injective ε) (S T : Subgroup M) :
    liftM ε ψ (S ⊔ T) = liftM ε ψ S ⊔ liftM ε ψ T := by
  unfold liftM
  rw [Subgroup.map_sup, pullG_sup hs hi]

theorem liftM_bot (hi : Function.Injective ε) : liftM ε ψ (⊥ : Subgroup M) = ⊥ := by
  unfold liftM
  rw [Subgroup.map_bot, pullG_bot hi]

theorem card_liftM (hs : Function.Surjective ε) (hi : Function.Injective ε)
    (hψ : Function.Injective ψ) (S : Subgroup M) : Nat.card (liftM ε ψ S) = Nat.card S := by
  unfold liftM
  rw [card_pullG hs hi, Subgroup.card_map_of_injective hψ]

theorem liftM_inf_centralizer (hs : Function.Surjective ε) (hi : Function.Injective ε)
    (hψ : Function.Injective ψ) (S T : Subgroup M) :
    liftM ε ψ S ⊓ Subgroup.centralizer (liftM ε ψ T : Set G) =
      liftM ε ψ (S ⊓ Subgroup.centralizer (T : Set M)) := by
  ext x
  constructor
  · rintro ⟨hxS, hxC⟩
    obtain ⟨hxL, s, hs', hsx⟩ := mem_liftM.1 hxS
    refine mem_liftM.2 ⟨hxL, s, ⟨hs', ?_⟩, hsx⟩
    apply Subgroup.mem_centralizer_iff.2
    intro t ht
    obtain ⟨y₀, hy₀⟩ := hs (ψ t)
    have hy : (y₀ : G) ∈ liftM ε ψ T := mem_liftM.2 ⟨y₀.2, t, ht, hy₀.symm⟩
    have hc := Subgroup.mem_centralizer_iff.1 hxC _ hy
    have h2 : y₀ * ⟨x, hxL⟩ = ⟨x, hxL⟩ * y₀ := Subtype.ext hc
    have h3 : ψ t * ψ s = ψ s * ψ t := by
      rw [← hy₀, hsx, ← map_mul, ← map_mul, h2]
    exact hψ (by rw [map_mul, map_mul]; exact h3)
  · intro hx
    obtain ⟨hxL, s, ⟨hs', hsC⟩, hsx⟩ := mem_liftM.1 hx
    refine ⟨mem_liftM.2 ⟨hxL, s, hs', hsx⟩, ?_⟩
    intro y hy
    obtain ⟨hyL, t, ht, hty⟩ := mem_liftM.1 hy
    have hst : t * s = s * t := Subgroup.mem_centralizer_iff.1 hsC t ht
    have : (⟨y, hyL⟩ : ↥L) * ⟨x, hxL⟩ = ⟨x, hxL⟩ * ⟨y, hyL⟩ := hi (by
      rw [map_mul, map_mul, ← hty, ← hsx, ← map_mul, ← map_mul, hst])
    exact congrArg Subtype.val this

theorem relIndex_liftM [Finite G] [Finite M] (hs : Function.Surjective ε)
    (hi : Function.Injective ε) (hψ : Function.Injective ψ) (S T : Subgroup M) :
    (liftM ε ψ S).relIndex (liftM ε ψ T) = S.relIndex T := by
  have h1 := Subgroup.relIndex_mul_card (H := liftM ε ψ S) (K := liftM ε ψ T)
  have h2 := Subgroup.relIndex_mul_card (H := S) (K := T)
  rw [← liftM_inf hψ, card_liftM hs hi hψ, card_liftM hs hi hψ] at h1
  have hpos : 0 < Nat.card ↥(S ⊓ T) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

theorem conjBy_liftM (S : Subgroup M) (g : M) (l : ↥L) (hl : ε l = ψ g) :
    conjBy (l : G) (liftM ε ψ S) = liftM ε ψ (S.map (MulAut.conj g).toMonoidHom) := by
  ext x
  rw [Equivariance.mem_conjBy, mem_liftM, mem_liftM]
  constructor
  · rintro ⟨hx, s, hs', hsx⟩
    have hxL : x ∈ L := by
      have := L.mul_mem (L.mul_mem l.2 hx) (L.inv_mem l.2)
      simpa [mul_assoc] using this
    refine ⟨hxL, g * s * g⁻¹, ⟨s, hs', rfl⟩, ?_⟩
    have h1 : ε ⟨(l : G)⁻¹ * x * l, hx⟩ = (ψ g)⁻¹ * ε ⟨x, hxL⟩ * ψ g := by
      have : (⟨(l : G)⁻¹ * x * l, hx⟩ : ↥L) = l⁻¹ * ⟨x, hxL⟩ * l := rfl
      rw [this, map_mul, map_mul, map_inv, hl]
    rw [h1] at hsx
    have : ε ⟨x, hxL⟩ = ψ g * ψ s * (ψ g)⁻¹ := by
      rw [hsx]
      group
    rw [this, ← map_mul, ← map_inv, ← map_mul]
  · rintro ⟨hxL, _, ⟨s, hs', rfl⟩, hsx⟩
    have hx : (l : G)⁻¹ * x * l ∈ L := by
      have := L.mul_mem (L.mul_mem (L.inv_mem l.2) hxL) l.2
      simpa using this
    refine ⟨hx, s, hs', ?_⟩
    have h1 : ε ⟨(l : G)⁻¹ * x * l, hx⟩ = (ψ g)⁻¹ * ε ⟨x, hxL⟩ * ψ g := by
      have : (⟨(l : G)⁻¹ * x * l, hx⟩ : ↥L) = l⁻¹ * ⟨x, hxL⟩ * l := rfl
      rw [this, map_mul, map_mul, map_inv, hl]
    rw [h1, ← hsx]
    show ψ s = (ψ g)⁻¹ * ψ (g * s * g⁻¹) * ψ g
    rw [map_mul, map_mul, map_inv]
    group

@[expose] noncomputable def liftEquiv (hs : Function.Surjective ε) (hi : Function.Injective ε)
    (hψ : Function.Injective ψ) (S : Subgroup M) : ↥(liftM ε ψ S) ≃* ↥S :=
  have hbij : Function.Bijective (ε.subgroupComap (S.map ψ)) := by
    refine ⟨fun a b hab => Subtype.ext (hi (congrArg Subtype.val hab)), fun q => ?_⟩
    obtain ⟨x, hx⟩ := hs q.1
    exact ⟨⟨x, by rw [Subgroup.mem_comap, hx]; exact q.2⟩, Subtype.ext hx⟩
  ((((Subgroup.subgroupOfEquivOfLe (pullG_le ε (S.map ψ))).symm.trans
    (MulEquiv.subgroupCongr (subgroupOf_pullG ε (S.map ψ)))).trans
    (MulEquiv.ofBijective (ε.subgroupComap (S.map ψ)) hbij)).trans
    (Subgroup.equivMapOfInjective S ψ hψ).symm)

theorem liftM_top (hψs : Function.Surjective ψ) : liftM ε ψ (⊤ : Subgroup M) = L := by
  refine le_antisymm (liftM_le _) fun x hx => ?_
  obtain ⟨s, hs'⟩ := hψs (ε ⟨x, hx⟩)
  exact mem_liftM.2 ⟨hx, s, Subgroup.mem_top s, hs'⟩

end

omit [Group M] in
theorem isElementaryAbelian_of_mulEquiv {p : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hX : IsElementaryAbelian p X) : IsElementaryAbelian p Y :=
  CFSG.IsElementaryAbelian.of_mulEquiv e hX

theorem isElementaryAbelian_liftM {ε : ↥L →* P} {ψ : M →* P} {p : ℕ}
    (hs : Function.Surjective ε) (hi : Function.Injective ε) (hψ : Function.Injective ψ)
    {S : Subgroup M} (hS : IsElementaryAbelian p ↥S) : IsElementaryAbelian p ↥(liftM ε ψ S) :=
  isElementaryAbelian_of_mulEquiv (liftEquiv hs hi hψ S).symm hS

end CFSG.RankThree.PartOne.K1320
