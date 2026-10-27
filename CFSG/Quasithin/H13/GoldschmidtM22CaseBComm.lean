module

public import CFSG.Quasithin.H13.GoldschmidtM22CaseBSign
public import CFSG.Quasithin.H13.GoldschmidtM22CaseBAct

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {V L : Subgroup G}

theorem le_actTriv (hLN : L ≤ Subgroup.normalizer (V : Set G)) (hLO : IsOTwoPerfect L)
    (hQ : ∀ q ∈ Subgroup.centralizer (V : Set G), ∃ k : ℕ, q ^ 2 ^ k = 1)
    (hN : ∀ n ∈ Subgroup.normalizer (V : Set G),
      ∃ c ∈ actTriv V, ∃ q ∈ Subgroup.centralizer (V : Set G), n = c * q) :
    L ≤ actTriv V := by
  let X : Subgroup G := L ⊓ actTriv V
  have hXL : X ≤ L := inf_le_left
  have hnorm : (X.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hXL]
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hx, hxC⟩
      exact ⟨L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl), conj_mem_actTriv (hLN hl) hxC⟩
    · rintro ⟨hx, hxC⟩
      have hxL : x ∈ L := by
        have := L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl
        simpa [mul_assoc] using this
      exact ⟨hxL, (mem_actTriv_iff_conj (hLN hl)).mpr hxC⟩
  have hX : X = L := hLO X hXL hnorm fun x hx => by
    obtain ⟨c, hc, q, hq, rfl⟩ := hN x (hLN hx)
    obtain ⟨k, hk⟩ := hQ q hq
    obtain ⟨c', hc', hcq⟩ := CFSG.Quasithin.A4.exists_pow_mul_eq hc
      (mem_normalizer_actTriv ((Subgroup.centralizer_le_normalizer _) hq)) (2 ^ k)
    exact ⟨k, L.pow_mem hx _, by rw [hcq, hk, mul_one]; exact hc'⟩
  intro l hl
  have : l ∈ X := hX ▸ hl
  exact this.2

@[expose] def commHom (l : G) (hl : ∀ q ∈ Subgroup.centralizer (V : Set G), l * q * l⁻¹ * q⁻¹ ∈ V) :
    ↥(Subgroup.centralizer (V : Set G)) →* ↥V where
  toFun q := ⟨l * q * l⁻¹ * q⁻¹, hl q q.2⟩
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    have hb : (l * (b : G) * l⁻¹ * (b : G)⁻¹) * (a : G) =
        (a : G) * (l * (b : G) * l⁻¹ * (b : G)⁻¹) :=
      Subgroup.mem_centralizer_iff.mp a.2 _ (hl b b.2)
    calc l * ((a : G) * b) * l⁻¹ * ((a : G) * b)⁻¹
        = (l * a * l⁻¹ * (a : G)⁻¹) * ((a : G) * (l * b * l⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by
          group
      _ = (l * a * l⁻¹ * (a : G)⁻¹) * (l * b * l⁻¹ * (b : G)⁻¹) := by rw [← hb]; group

theorem commHom_apply {l : G} {hl : ∀ q ∈ Subgroup.centralizer (V : Set G), l * q * l⁻¹ * q⁻¹ ∈ V}
    (q : ↥(Subgroup.centralizer (V : Set G))) :
    ((commHom l hl q : ↥V) : G) = l * q * l⁻¹ * (q : G)⁻¹ := rfl

theorem isElemAbelian_centralizer {T : Subgroup G} (hV : IsElemAbelian 2 V)
    (hQT : Subgroup.centralizer (V : Set G) ≤ T)
    (hCT : ∀ x ∈ T, (∀ l ∈ L, l * x = x * l) → x = 1)
    (hcomm : ∀ l ∈ L, ∀ q ∈ Subgroup.centralizer (V : Set G), l * q * l⁻¹ * q⁻¹ ∈ V) :
    IsElemAbelian 2 (Subgroup.centralizer (V : Set G)) := by
  have key : ∀ (l : G) (hl : l ∈ L) (z : ↥(Subgroup.centralizer (V : Set G))),
      commHom l (hcomm l hl) z = 1 → l * (z : G) = (z : G) * l := by
    intro l hl z hz
    have h1 := congrArg Subtype.val hz
    rw [commHom_apply] at h1
    simp only [Subgroup.coe_one] at h1
    have h2 : l * (z : G) * l⁻¹ = z := mul_inv_eq_one.mp h1
    calc l * (z : G) = (l * z * l⁻¹) * l := by group
      _ = (z : G) * l := by rw [h2]
  have hZ : ∀ z : ↥(Subgroup.centralizer (V : Set G)),
      (∀ (l : G) (hl : l ∈ L), commHom l (hcomm l hl) z = 1) → (z : G) = 1 := fun z hz =>
    hCT z (hQT z.2) fun l hl => key l hl z (hz l hl)
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · have h1 : (⁅x, y⁆ : ↥(Subgroup.centralizer (V : Set G))) = 1 :=
      Subtype.ext (hZ _ fun l hl => by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (hV.1.is_comm.comm _ _))
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  · have h1 : ((⟨x, hx⟩ : ↥(Subgroup.centralizer (V : Set G))) ^ 2) = 1 :=
      Subtype.ext (hZ _ fun l hl => by
        rw [map_pow]
        exact Subtype.ext (hV.2 _ (commHom l (hcomm l hl) ⟨x, hx⟩).2))
    simpa using congrArg Subtype.val h1

end CFSG.Quasithin.H13.GM22
