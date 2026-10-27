module

public import CFSG.Quasithin.Background.RonanE111Cmod
public import CFSG.Quasithin.Background.RonanE111Diag

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N
  CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement

variable {Q : Type} [Group Q]

section Generic

variable {G : Type} [Group G]

theorem transfer_eq_of_mk_eq {H K : Subgroup G} [K.Normal] (hHK : H ⊓ K = ⊥) {y z : G}
    (hy : y ∈ H) (hz : z ∈ H) (h : QuotientGroup.mk' K y = QuotientGroup.mk' K z) :
    y = z := by
  have hmem : y⁻¹ * z ∈ H := H.mul_mem (H.inv_mem hy) hz
  have h1 : QuotientGroup.mk' K (y⁻¹ * z) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have h3 : y⁻¹ * z ∈ H ⊓ K := ⟨hmem, (QuotientGroup.eq_one_iff _).mp h1⟩
  rw [hHK, Subgroup.mem_bot] at h3
  exact inv_mul_eq_one.mp h3

theorem transfer_mk_comm_iff {H K : Subgroup G} [H.Normal] [K.Normal] (hHK : H ⊓ K = ⊥)
    {a b : G} (hb : b ∈ H) :
    QuotientGroup.mk' K b * QuotientGroup.mk' K a = QuotientGroup.mk' K a * QuotientGroup.mk' K b ↔
      b * a = a * b := by
  constructor
  · intro h
    have hconj : a * b * a⁻¹ ∈ H := Subgroup.Normal.conj_mem inferInstance b hb a
    have hc : a * b * a⁻¹ * b⁻¹ ∈ H := H.mul_mem hconj (H.inv_mem hb)
    have hπ : QuotientGroup.mk' K (a * b * a⁻¹ * b⁻¹) = QuotientGroup.mk' K 1 := by
      rw [map_one]
      simp only [map_mul, map_inv]
      rw [← h]
      group
    have hc1 : a * b * a⁻¹ * b⁻¹ = 1 := transfer_eq_of_mk_eq hHK hc H.one_mem hπ
    have hab : a * b = b * a := by
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [hc1, one_mul]
    exact hab.symm
  · intro h
    rw [← map_mul, ← map_mul, h]

theorem transfer_centralizer {H K T : Subgroup G} [H.Normal] [K.Normal] (hHK : H ⊓ K = ⊥)
    (hTH : T ≤ H) (y : G) :
    QuotientGroup.mk' K y ∈ Subgroup.centralizer
        ((T.map (QuotientGroup.mk' K) : Subgroup (G ⧸ K)) : Set (G ⧸ K)) ↔
      y ∈ Subgroup.centralizer (T : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h t ht
    exact (transfer_mk_comm_iff hHK (hTH ht)).mp
      (h (QuotientGroup.mk' K t) (Subgroup.mem_map_of_mem (QuotientGroup.mk' K) ht))
  · intro h z hz
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hz
    exact (transfer_mk_comm_iff hHK (hTH ht)).mpr (h t ht)

theorem transfer_normalizer {H K T : Subgroup G} [H.Normal] [K.Normal] (hHK : H ⊓ K = ⊥)
    (hTH : T ≤ H) (y : G) :
    QuotientGroup.mk' K y ∈ Subgroup.normalizer
        ((T.map (QuotientGroup.mk' K) : Subgroup (G ⧸ K)) : Set (G ⧸ K)) ↔
      y ∈ Subgroup.normalizer (T : Set G) := by
  have fwd : ∀ z : G, QuotientGroup.mk' K z ∈ Subgroup.normalizer
      ((T.map (QuotientGroup.mk' K) : Subgroup (G ⧸ K)) : Set (G ⧸ K)) →
      ∀ t ∈ T, z * t * z⁻¹ ∈ T := by
    intro z hz t ht
    have h1 : QuotientGroup.mk' K z * QuotientGroup.mk' K t * (QuotientGroup.mk' K z)⁻¹ ∈
        T.map (QuotientGroup.mk' K) :=
      (Subgroup.mem_normalizer_iff.mp hz (QuotientGroup.mk' K t)).mp
        (Subgroup.mem_map_of_mem (QuotientGroup.mk' K) ht)
    have h2 : QuotientGroup.mk' K (z * t * z⁻¹) =
        QuotientGroup.mk' K z * QuotientGroup.mk' K t * (QuotientGroup.mk' K z)⁻¹ := by
      simp only [map_mul, map_inv]
    rw [← h2] at h1
    obtain ⟨t', ht', hpt⟩ := Subgroup.mem_map.mp h1
    have hzt : z * t * z⁻¹ ∈ H := Subgroup.Normal.conj_mem inferInstance t (hTH ht) z
    have heq : t' = z * t * z⁻¹ := transfer_eq_of_mk_eq hHK (hTH ht') hzt hpt
    rw [← heq]
    exact ht'
  constructor
  · intro hy
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact fwd y hy h hh
    · intro hh
      have hinv : QuotientGroup.mk' K y⁻¹ ∈ Subgroup.normalizer
          ((T.map (QuotientGroup.mk' K) : Subgroup (G ⧸ K)) : Set (G ⧸ K)) := by
        rw [map_inv]
        exact inv_mem hy
      have hfin := fwd y⁻¹ hinv (y * h * y⁻¹) hh
      have e : y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ = h := by group
      rw [e] at hfin
      exact hfin
  · intro hy
    exact Subgroup.le_normalizer_map (QuotientGroup.mk' K) (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)

theorem transfer_normalizer_of_le {N T : Subgroup G} [N.Normal] (hNT : N ≤ T) (y : G) :
    QuotientGroup.mk' N y ∈ Subgroup.normalizer
        ((T.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) ↔
      y ∈ Subgroup.normalizer (T : Set G) := by
  have fwd : ∀ z : G, QuotientGroup.mk' N z ∈ Subgroup.normalizer
      ((T.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) →
      ∀ t ∈ T, z * t * z⁻¹ ∈ T := by
    intro z hz t ht
    have h1 : QuotientGroup.mk' N z * QuotientGroup.mk' N t * (QuotientGroup.mk' N z)⁻¹ ∈
        T.map (QuotientGroup.mk' N) :=
      (Subgroup.mem_normalizer_iff.mp hz (QuotientGroup.mk' N t)).mp
        (Subgroup.mem_map_of_mem (QuotientGroup.mk' N) ht)
    have h2 : QuotientGroup.mk' N (z * t * z⁻¹) =
        QuotientGroup.mk' N z * QuotientGroup.mk' N t * (QuotientGroup.mk' N z)⁻¹ := by
      simp only [map_mul, map_inv]
    rw [← h2] at h1
    obtain ⟨t', ht', hpt⟩ := Subgroup.mem_map.mp h1
    have h3 : QuotientGroup.mk' N (t'⁻¹ * (z * t * z⁻¹)) = 1 := by
      rw [map_mul, map_inv, hpt, inv_mul_cancel]
    have h4 : t'⁻¹ * (z * t * z⁻¹) ∈ N := (QuotientGroup.eq_one_iff _).mp h3
    have h5 : t' * (t'⁻¹ * (z * t * z⁻¹)) ∈ T := T.mul_mem ht' (hNT h4)
    have e : t' * (t'⁻¹ * (z * t * z⁻¹)) = z * t * z⁻¹ := by group
    rw [e] at h5
    exact h5
  constructor
  · intro hy
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact fwd y hy h hh
    · intro hh
      have hinv : QuotientGroup.mk' N y⁻¹ ∈ Subgroup.normalizer
          ((T.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
        rw [map_inv]
        exact inv_mem hy
      have hfin := fwd y⁻¹ hinv (y * h * y⁻¹) hh
      have e : y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ = h := by group
      rw [e] at hfin
      exact hfin
  · intro hy
    exact Subgroup.le_normalizer_map (QuotientGroup.mk' N) (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)

theorem transfer_card_actOn_of_hom {G₁ G₂ : Type} [Group G₁] [Group G₂] (ρ : G₁ →* G₂)
    {B K : Subgroup G₁} {Sb Ab : Subgroup G₂}
    (hB : ∀ x ∈ B, ρ x ∈ Ab ⊓ Subgroup.normalizer (Sb : Set G₂))
    (hsurj : ∀ u ∈ Ab ⊓ Subgroup.normalizer (Sb : Set G₂), ∃ x ∈ B, ρ x = u)
    (hK : ∀ x ∈ B, x ∈ K ↔ ρ x ∈ Subgroup.centralizer (Sb : Set G₂)) :
    Nat.card ↥(actOn Sb Ab) = K.relIndex B := by
  set φ := conjAut (inf_le_right : Ab ⊓ Subgroup.normalizer (Sb : Set G₂) ≤
    Subgroup.normalizer (Sb : Set G₂))
  let ψ : ↥B →* ↥(Ab ⊓ Subgroup.normalizer (Sb : Set G₂)) :=
    { toFun := fun x => ⟨ρ x, hB x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hψs : Function.Surjective ψ := by
    intro v
    obtain ⟨x, hxB, hx⟩ := hsurj v.1 v.2
    exact ⟨⟨x, hxB⟩, Subtype.ext hx⟩
  have hrange : (φ.comp ψ).range = φ.range := by
    ext u
    constructor
    · intro hu
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hu
      exact MonoidHom.mem_range.mpr ⟨ψ x, rfl⟩
    · intro hu
      obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hu
      obtain ⟨x, hx⟩ := hψs v
      exact MonoidHom.mem_range.mpr ⟨x, by rw [MonoidHom.comp_apply, hx]⟩
  have key : ∀ x : ↥B, φ (ψ x) = 1 ↔ ρ x ∈ Subgroup.centralizer (Sb : Set G₂) := by
    intro x
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h d hd
      have h1 : ρ x * d * (ρ x)⁻¹ = d :=
        congrArg (fun f : MulAut ↥Sb => ((f ⟨d, hd⟩ : ↥Sb) : G₂)) h
      calc d * ρ x = (ρ x * d * (ρ x)⁻¹) * ρ x := by rw [h1]
        _ = ρ x * d := by group
    · intro h
      refine MulEquiv.ext fun u => Subtype.ext ?_
      have h1 : (u : G₂) * ρ x = ρ x * (u : G₂) := h u u.2
      show ρ x * (u : G₂) * (ρ x)⁻¹ = (u : G₂)
      rw [← h1]
      group
  have hker : (φ.comp ψ).ker = K.subgroupOf B := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply]
    exact (key x).trans (hK x x.2).symm
  show Nat.card ↥φ.range = K.relIndex B
  rw [← hrange, ← Subgroup.index_ker, hker]
  rfl

end Generic

section Transfer

variable {Y D : Subgroup Q} [Y.Normal]

theorem mem_centralizer_quot_iff [D.Normal]
    (hZ : D.map (QuotientGroup.mk' Y) ⊓ centMod D Y = ⊥) {S : Subgroup Q} (hYS : Y ≤ S)
    (hSD : S ≤ D) (x : Q) :
    QuotientGroup.mk' (centMod D Y) (QuotientGroup.mk' Y x) ∈
        Subgroup.centralizer ((((S.map (QuotientGroup.mk' Y)).map
          (QuotientGroup.mk' (centMod D Y)) : Subgroup _)) : Set _) ↔ x ∈ Cmod S Y := by
  haveI : (D.map (QuotientGroup.mk' Y)).Normal :=
    Subgroup.Normal.map ‹D.Normal› _ (QuotientGroup.mk'_surjective Y)
  rw [transfer_centralizer hZ (Subgroup.map_mono (f := QuotientGroup.mk' Y) hSD)
    (QuotientGroup.mk' Y x)]
  exact Iff.rfl

theorem mem_normalizer_quot_iff [D.Normal]
    (hZ : D.map (QuotientGroup.mk' Y) ⊓ centMod D Y = ⊥) {S : Subgroup Q} (hYS : Y ≤ S)
    (hSD : S ≤ D) (x : Q) :
    QuotientGroup.mk' (centMod D Y) (QuotientGroup.mk' Y x) ∈
        Subgroup.normalizer ((((S.map (QuotientGroup.mk' Y)).map
          (QuotientGroup.mk' (centMod D Y)) : Subgroup _)) : Set _) ↔
      x ∈ Subgroup.normalizer (S : Set Q) := by
  haveI : (D.map (QuotientGroup.mk' Y)).Normal :=
    Subgroup.Normal.map ‹D.Normal› _ (QuotientGroup.mk'_surjective Y)
  rw [transfer_normalizer hZ (Subgroup.map_mono (f := QuotientGroup.mk' Y) hSD)
    (QuotientGroup.mk' Y x)]
  exact transfer_normalizer_of_le hYS x

theorem card_actOn_quot [D.Normal]
    (hZ : D.map (QuotientGroup.mk' Y) ⊓ centMod D Y = ⊥) {S : Subgroup Q} (hYS : Y ≤ S)
    (hSD : S ≤ D) (A : Subgroup Q) :
    Nat.card ↥(actOn ((S.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (centMod D Y)))
        ((A.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (centMod D Y)))) =
      (A ⊓ Subgroup.normalizer (S : Set Q) ⊓ Cmod S Y).relIndex
        (A ⊓ Subgroup.normalizer (S : Set Q)) := by
  haveI : (D.map (QuotientGroup.mk' Y)).Normal :=
    Subgroup.Normal.map ‹D.Normal› _ (QuotientGroup.mk'_surjective Y)
  refine transfer_card_actOn_of_hom
    ((QuotientGroup.mk' (centMod D Y)).comp (QuotientGroup.mk' Y))
    (B := A ⊓ Subgroup.normalizer (S : Set Q))
    (K := A ⊓ Subgroup.normalizer (S : Set Q) ⊓ Cmod S Y) ?_ ?_ ?_
  · intro x hx
    exact ⟨Subgroup.mem_map.mpr ⟨QuotientGroup.mk' Y x, Subgroup.mem_map.mpr ⟨x, hx.1, rfl⟩, rfl⟩,
      (mem_normalizer_quot_iff hZ hYS hSD x).mpr hx.2⟩
  · rintro u ⟨hu1, hu2⟩
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu1
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hv
    exact ⟨a, ⟨ha, (mem_normalizer_quot_iff hZ hYS hSD a).mp hu2⟩, rfl⟩
  · intro x hx
    rw [MonoidHom.comp_apply, mem_centralizer_quot_iff hZ hYS hSD x]
    exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

end Transfer

end CFSG.Quasithin.RonanE111
