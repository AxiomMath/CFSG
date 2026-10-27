module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B19Normal
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin.B610T.TwoBlk

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Preimage

variable {G : Type} [Group G] {V H : Subgroup G} (hV : IsElemAbelian 2 V)
  (hHN : H ≤ Subgroup.normalizer (V : Set G))

theorem burnsideB610_convI_conj {g x : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (hx : x ∈ Subgroup.normalizer (V : Set G))
    (h : g⁻¹ * x * g ∈ Subgroup.normalizer (V : Set G)) :
    convI hV ⟨g⁻¹ * x * g, h⟩ = (convI hV ⟨g, hg⟩)⁻¹ * convI hV ⟨x, hx⟩ * convI hV ⟨g, hg⟩ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

include hHN in
theorem burnsideB610_cjSub_preI {h : G} (hh : h ∈ H) (B : Subgroup (MulAut (IntMod V hV))) :
    cjSub h (preI hV H hHN B) =
      preI hV H hHN (B.map (MulAut.conj (convI hV ⟨h, hHN hh⟩)).toMonoidHom) := by
  have hHconj : ∀ x : G, h⁻¹ * x * h ∈ H ↔ x ∈ H := by
    intro x
    constructor
    · intro hx
      have := H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)
      simpa [mul_assoc] using this
    · intro hx
      exact H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh
  ext x
  rw [mem_cjSub]
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := (mem_preI hV).1 hx
    have hxH := (hHconj x).1 hx1
    refine (mem_preI hV).2 ⟨hxH, ?_⟩
    rw [B19.mem_map_conj]
    have e := burnsideB610_convI_conj hV (hHN hh) (hHN hxH) (hHN hx1)
    show (convI hV ⟨h, hHN hh⟩)⁻¹ * convI hV ⟨x, hHN hxH⟩ * convI hV ⟨h, hHN hh⟩ ∈ B
    rw [← e]
    exact hx2
  · intro hx
    obtain ⟨hxH, hx2⟩ := (mem_preI hV).1 hx
    rw [B19.mem_map_conj] at hx2
    refine (mem_preI hV).2 ⟨(hHconj x).2 hxH, ?_⟩
    have e := burnsideB610_convI_conj hV (hHN hh) (hHN hxH) (hHN ((hHconj x).2 hxH))
    show convI hV ⟨h⁻¹ * x * h, hHN ((hHconj x).2 hxH)⟩ ∈ B
    rw [e]
    exact hx2

include hHN in
theorem burnsideB610_mem_normalizer_preI {h : G} (hh : h ∈ H)
    {B : Subgroup (MulAut (IntMod V hV))}
    (hB : convI hV ⟨h, hHN hh⟩ ∈ Subgroup.normalizer (B : Set (MulAut (IntMod V hV)))) :
    h ∈ Subgroup.normalizer (preI hV H hHN B : Set G) := by
  rw [B2F.mem_normalizer_iff_cjSub_eq, burnsideB610_cjSub_preI hV hHN hh B]
  congr 1
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hB

theorem burnsideB610_convI_mem_normalizer_autI {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    {Y : Subgroup G} (hgY : g ∈ Subgroup.normalizer (Y : Set G)) :
    convI hV ⟨g, hg⟩ ∈ Subgroup.normalizer (autI hV Y : Set (MulAut (IntMod V hV))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine (autI_cjSub hV hg Y).trans ?_
  rw [B2F.mem_normalizer_iff_cjSub_eq.mp hgY]

end Preimage

section Blocks

variable {W : Type} [CommGroup W]

@[expose] def burnsideB610_blocks (X Φ : Subgroup (MulAut W)) : Set (Subgroup (MulAut W)) :=
  {B | ∃ t ∈ B19.tvSet X Φ, B = B19.GOf Φ t}

variable [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {X Φ : Subgroup (MulAut W)} (hS : B19.Setting X Φ)
include hW hS

theorem burnsideB610_GOf_map_conj {t g : MulAut W} (ht : t ∈ B19.tvSet X Φ) (hg : g ∈ X)
    (hF : (B19.FOf Φ t).map (MulAut.conj g).toMonoidHom = B19.FOf Φ t) :
    (B19.GOf Φ t).map (MulAut.conj g).toMonoidHom = B19.GOf Φ t := by
  rw [hS.GOf_conj hg t]
  refine hS.GOf_eq_of_FOf_eq hW (hS.conj_mem_tvSet hg ht) ht ?_
  rw [← hS.FOf_conj hg t, hF]

theorem burnsideB610_ffJ_le_normalizer {t : MulAut W} (ht : t ∈ B19.tvSet X Φ) :
    ffJ X ≤ Subgroup.normalizer (B19.GOf Φ t : Set (MulAut W)) := by
  refine iSup₂_le fun A hA => fun a ha => ?_
  exact B19.mem_normalizer_of_map_conj_eq (burnsideB610_GOf_map_conj hW hS ht (hA.1 ha)
    (hS.map_conj_FOf hW hA ht ha))

theorem burnsideB610_map_conj_mem_blocks {B : Subgroup (MulAut W)}
    (hB : B ∈ burnsideB610_blocks X Φ) {g : MulAut W} (hg : g ∈ X) :
    B.map (MulAut.conj g).toMonoidHom ∈ burnsideB610_blocks X Φ := by
  obtain ⟨t, ht, rfl⟩ := hB
  exact ⟨g * t * g⁻¹, hS.conj_mem_tvSet hg ht, hS.GOf_conj hg t⟩

theorem burnsideB610_block_le {B : Subgroup (MulAut W)} (hB : B ∈ burnsideB610_blocks X Φ) :
    B ≤ X := by
  obtain ⟨t, ht, rfl⟩ := hB
  exact hS.GOf_le hW ht

theorem burnsideB610_mem_FOf_of_cube {t z : MulAut W} (ht : t ∈ B19.tvSet X Φ)
    (hz : z ∈ B19.GOf Φ t) (hz3 : z ^ 3 = 1) : z ∈ B19.FOf Φ t := by
  obtain ⟨y, w, h⟩ := hS.exists_tvBlock hW ht
  rw [h.GOf_eq] at hz
  rw [h.FOf_eq]
  have hsq := h.sq hW
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hsq
  rcases B19.mem_or_mul_mem_of_mem_sup hsq (fun f hf => by
      rw [h.inv_zpowers hf]; exact Subgroup.inv_mem _ hf) hz with h1 | h1
  · exact h1
  · have htc : t * (z * t) * t⁻¹ = (z * t)⁻¹ := h.inv_zpowers h1
    have hzz : z * z = 1 := by
      have e : z * z = (z * t) * (t * (z * t) * t⁻¹) := by
        rw [htinv]
        calc z * z = z * (t * t) * z * (t * t) := by rw [hsq, mul_one, mul_one]
          _ = (z * t) * (t * (z * t) * t) := by group
      rw [e, htc, mul_inv_cancel]
    have hz1 : z = 1 := by
      calc z = z ^ 3 * (z * z)⁻¹ := by rw [pow_succ, pow_two]; group
        _ = 1 := by rw [hz3, hzz]; group
    rw [hz1]
    exact Subgroup.one_mem _

theorem burnsideB610_mem_normalizer_FOf {t g : MulAut W} (ht : t ∈ B19.tvSet X Φ)
    (hg : g ∈ Subgroup.normalizer (B19.GOf Φ t : Set (MulAut W))) :
    g ∈ Subgroup.normalizer (B19.FOf Φ t : Set (MulAut W)) := by
  obtain ⟨y, w, h⟩ := hS.exists_tvBlock hW ht
  have hcube : ∀ f ∈ B19.FOf Φ t, f ^ 3 = 1 := by
    intro f hf
    rw [h.FOf_eq] at hf
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h.x3, one_zpow]
  rw [Subgroup.mem_normalizer_iff]
  intro f
  constructor
  · intro hf
    refine burnsideB610_mem_FOf_of_cube hW hS ht
      ((Subgroup.mem_normalizer_iff.mp hg f).mp (B19.FOf_le_GOf hf)) ?_
    rw [conj_pow, hcube f hf]
    group
  · intro hf
    have hfG : f ∈ B19.GOf Φ t :=
      (Subgroup.mem_normalizer_iff.mp hg f).mpr (B19.FOf_le_GOf hf)
    refine burnsideB610_mem_FOf_of_cube hW hS ht hfG ?_
    have h1 := hcube _ hf
    rw [conj_pow] at h1
    have h2 : f ^ 3 = g⁻¹ * (g * f ^ 3 * g⁻¹) * g := by group
    rw [h2, h1]
    group

theorem burnsideB610_GOf_le_stabSub {t : MulAut W} (ht : t ∈ B19.tvSet X Φ) :
    B19.GOf Φ t ≤ stabSub (commV (B19.FOf Φ t)) := by
  intro a ha
  have hmap : (B19.FOf Φ t).map (MulAut.conj a).toMonoidHom = B19.FOf Φ t :=
    B19.map_conj_eq_of_mem_normalizer (hS.GOf_le_normalizer hW ht ha)
  have hMa : (commV (B19.FOf Φ t)).map a.toMonoidHom = commV (B19.FOf Φ t) := by
    rw [← B19.commV_map_conj, hmap]
  intro u
  constructor
  · intro hu
    rw [← hMa] at hu
    obtain ⟨u', hu', hau⟩ := hu
    rw [← a.injective hau]
    exact hu'
  · intro hu
    rw [← hMa]
    exact ⟨u, hu, rfl⟩

theorem burnsideB610_actsAsNatural {B : Subgroup (MulAut W)}
    (hB : B ∈ burnsideB610_blocks X Φ) : ActsAsNaturalL2 B (commV B) := by
  obtain ⟨t, ht, rfl⟩ := hB
  rw [hS.commV_GOf hW ht]
  exact actsAsNaturalL2_of_full hW (hS.card_commV_FOf hW ht)
    (burnsideB610_GOf_le_stabSub hW hS ht) (hS.GOf_inf_centSub hW ht) (hS.autSub_GOf hW ht)

theorem burnsideB610_commV_inf_fixV {B : Subgroup (MulAut W)}
    (hB : B ∈ burnsideB610_blocks X Φ) : commV B ⊓ fixV B = ⊥ := by
  obtain ⟨t, ht, rfl⟩ := hB
  rw [hS.commV_GOf hW ht]
  refine le_bot_iff.1 ?_
  rw [← (hS.decomp_FOf hW ht).2, inf_comm]
  exact inf_le_inf_right _ (B1.fixV_le_fixV B19.FOf_le_GOf)

theorem burnsideB610_card_block {B : Subgroup (MulAut W)} (hB : B ∈ burnsideB610_blocks X Φ) :
    Nat.card B = 6 := by
  obtain ⟨t, ht, rfl⟩ := hB
  exact hS.card_GOf hW ht

theorem burnsideB610_FOf_ne {t t' : MulAut W} (ht : t ∈ B19.tvSet X Φ)
    (ht' : t' ∈ B19.tvSet X Φ) (hne : B19.GOf Φ t ≠ B19.GOf Φ t') :
    B19.FOf Φ t ≠ B19.FOf Φ t' := fun h => hne (hS.GOf_eq_of_FOf_eq hW ht ht' h)

theorem burnsideB610_block_comm {B B' : Subgroup (MulAut W)}
    (hB : B ∈ burnsideB610_blocks X Φ) (hB' : B' ∈ burnsideB610_blocks X Φ) (hne : B ≠ B') :
    ∀ a ∈ B, ∀ b ∈ B', a * b = b * a := by
  obtain ⟨t, ht, rfl⟩ := hB
  obtain ⟨t', ht', rfl⟩ := hB'
  exact hS.pair_comm hW ht ht' (burnsideB610_FOf_ne hW hS ht ht' hne)

theorem burnsideB610_block_centSub {B B' : Subgroup (MulAut W)}
    (hB : B ∈ burnsideB610_blocks X Φ) (hB' : B' ∈ burnsideB610_blocks X Φ) (hne : B ≠ B') :
    B' ≤ centSub (commV B) := by
  obtain ⟨t, ht, rfl⟩ := hB
  obtain ⟨t', ht', rfl⟩ := hB'
  rw [hS.commV_GOf hW ht]
  exact hS.pair_centSub hW ht ht' (burnsideB610_FOf_ne hW hS ht ht' hne)

theorem burnsideB610_eq_one_of_fix {t y : MulAut W} {w : W} (ht : t ∈ B19.tvSet X Φ)
    (h : B19.TvBlock Φ t y w) {m : W} (hm : m ∈ commV (B19.GOf Φ t)) (hym : y m = m) :
    m = 1 := by
  rw [hS.commV_GOf hW ht, h.FOf_eq, commV_eq_commSub] at hm
  exact (B19.zpowers_three_decomp hW h.x3).2.2.2.1 m hm hym

end Blocks

end CFSG.Quasithin.B610T.TwoBlk
