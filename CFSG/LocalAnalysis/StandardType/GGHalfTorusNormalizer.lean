module

public import CFSG.LocalAnalysis.StandardType.GGHalfBasic
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockPerm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

private theorem mem_normalizer_of_conj_mem {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {w : G} (h : ∀ b ∈ H, w * b * w⁻¹ ∈ H) :
    w ∈ Subgroup.normalizer (H : Set G) := by
  have hpow : ∀ n : ℕ, ∀ b ∈ H, w ^ n * b * (w ^ n)⁻¹ ∈ H := by
    intro n
    induction n with
    | zero => intro b hb; simpa using hb
    | succ n ih =>
      intro b hb
      have h1 := h _ (ih b hb)
      rw [pow_succ', _root_.mul_inv_rev]
      simpa only [mul_assoc] using h1
  have hinv : w⁻¹ = w ^ (Nat.card G - 1) := by
    have h1 : w ^ Nat.card G = 1 := pow_card_eq_one'
    have h2 : 1 ≤ Nat.card G := Nat.card_pos
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel h2, h1]
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨h b, fun hb => ?_⟩
  have h3 := hpow (Nat.card G - 1) (w * b * w⁻¹) hb
  rw [← hinv, inv_inv] at h3
  simpa [mul_assoc] using h3

private theorem map_le_of_act {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {A : Type} [Group A] {T : Subgroup A} {φ : A →* G} {L : Subgroup G}
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hp : p = 3) (hL : φ.range = L)
    (hact : ∀ b ∈ Bs, ∃ t ∈ T, ∀ l ∈ L, b * l * b⁻¹ = φ t * l * (φ t)⁻¹)
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hpow : ∀ a ∈ T, a ^ 3 = 1) : T.map φ ≤ Bs := by
  rintro x hx
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
  refine hstar (φ s) ?_ ?_
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨t, ht, htl⟩ := hact b hb
    have hsL : φ s ∈ L := by rw [← hL]; exact ⟨s, rfl⟩
    have hconj : b * φ s * b⁻¹ = φ s := by
      have h1 := htl (φ s) hsL
      rw [h1, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      rw [hcomm t ht s hs, mul_assoc, mul_inv_cancel, mul_one]
    calc b * φ s = b * φ s * b⁻¹ * b := by group
      _ = φ s * b := by rw [hconj]
  · rw [hp, ← map_pow, hpow s hs, map_one]

private theorem mem_normalizer_of_act {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {A : Type} [Group A] {T : Subgroup A} {φ : A →* G} {L : Subgroup G}
    (hTle : T.map φ ≤ Bs) (hL : φ.range = L)
    (hact : ∀ b ∈ Bs, ∃ t ∈ T, ∀ l ∈ L, b * l * b⁻¹ = φ t * l * (φ t)⁻¹)
    {a : A} (ha : ∀ t ∈ T, a * t * a⁻¹ ∈ T) :
    φ a ∈ Subgroup.normalizer (Bs : Set G) := by
  refine mem_normalizer_of_conj_mem fun b hb => ?_
  obtain ⟨t, ht, htl⟩ := hact b hb
  have haL : φ a ∈ L := by rw [← hL]; exact ⟨a, rfl⟩
  have hcL : ((φ t)⁻¹ * b) * φ a * ((φ t)⁻¹ * b)⁻¹ = φ a := by
    calc ((φ t)⁻¹ * b) * φ a * ((φ t)⁻¹ * b)⁻¹
        = (φ t)⁻¹ * (b * φ a * b⁻¹) * φ t := by group
      _ = (φ t)⁻¹ * (φ t * φ a * (φ t)⁻¹) * φ t := by rw [htl (φ a) haL]
      _ = φ a := by group
  have hcinv : ((φ t)⁻¹ * b) * (φ a)⁻¹ = (φ a)⁻¹ * ((φ t)⁻¹ * b) := by
    have hc : (φ t)⁻¹ * b * φ a = φ a * ((φ t)⁻¹ * b) := by
      calc (φ t)⁻¹ * b * φ a
          = (φ t)⁻¹ * b * φ a * ((φ t)⁻¹ * b)⁻¹ * ((φ t)⁻¹ * b) := by group
        _ = φ a * ((φ t)⁻¹ * b) := by rw [hcL]
    calc ((φ t)⁻¹ * b) * (φ a)⁻¹
        = (φ a)⁻¹ * ((φ a) * ((φ t)⁻¹ * b)) * (φ a)⁻¹ := by group
      _ = (φ a)⁻¹ * (((φ t)⁻¹ * b) * φ a) * (φ a)⁻¹ := by rw [← hc]
      _ = (φ a)⁻¹ * ((φ t)⁻¹ * b) := by group
  have hmain : φ a * b * (φ a)⁻¹ = φ (a * t * a⁻¹ * t⁻¹) * b := by
    calc φ a * b * (φ a)⁻¹
        = φ a * φ t * ((φ t)⁻¹ * b) * (φ a)⁻¹ := by group
      _ = φ a * φ t * (φ a)⁻¹ * ((φ t)⁻¹ * b) := by
            calc φ a * φ t * ((φ t)⁻¹ * b) * (φ a)⁻¹
                = (φ a * φ t) * (((φ t)⁻¹ * b) * (φ a)⁻¹) := by group
              _ = (φ a * φ t) * ((φ a)⁻¹ * ((φ t)⁻¹ * b)) := by rw [hcinv]
              _ = φ a * φ t * (φ a)⁻¹ * ((φ t)⁻¹ * b) := by group
      _ = φ (a * t * a⁻¹) * ((φ t)⁻¹ * b) := by
            conv_lhs => rw [← map_inv, ← map_mul, ← map_mul]
      _ = φ (a * t * a⁻¹) * (φ t)⁻¹ * b := by group
      _ = φ (a * t * a⁻¹ * t⁻¹) * b := by
            conv_lhs => rw [← map_inv, ← map_mul]
  rw [hmain]
  exact Bs.mul_mem (hTle (Subgroup.mem_map.mpr
    ⟨a * t * a⁻¹ * t⁻¹, T.mul_mem (ha t ht) (T.inv_mem ht), rfl⟩)) hb

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {m : ℕ} {y : G}
  {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂)

include h

theorem torusL_le : (halfTorus (m + 1 + 1)).map φ₁ ≤ Bs :=
  map_le_of_act h.cfg.2.1.2.2.2 h.nbr.2.1 h.coords.range₁ h.coords.actL
    (fun _ ha _ hb => halfTorus_comm ha hb) fun _ ha => halfTorus_pow_three ha

theorem torusK_le : (halfTorusK (m + 1 + 1)).map φ₂ ≤ Bs :=
  map_le_of_act h.cfg.2.1.2.2.2 h.nbr.2.1 h.coords.range₂ h.coords.actK
    (fun _ ha _ hb => halfTorusK_comm ha hb) fun _ ha => halfTorusK_pow_three ha

theorem mem_normalizer_L {a : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (ha : ∀ t ∈ halfTorus (m + 1 + 1), a * t * a⁻¹ ∈ halfTorus (m + 1 + 1)) :
    φ₁ a ∈ Subgroup.normalizer (Bs : Set G) :=
  mem_normalizer_of_act (torusL_le h) h.coords.range₁ h.coords.actL ha

theorem mem_normalizer_K {a : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (ha : ∀ t ∈ halfTorusK (m + 1 + 1), a * t * a⁻¹ ∈ halfTorusK (m + 1 + 1)) :
    φ₂ a ∈ Subgroup.normalizer (Bs : Set G) :=
  mem_normalizer_of_act (torusK_le h) h.coords.range₂ h.coords.actK ha

theorem s0_mem_normalizer :
    φ₁ (weylRep (m + 1 + 1) F2 ⟨0, by omega⟩) ∈ Subgroup.normalizer (Bs : Set G) :=
  h.mem_normalizer_L fun _ ht => weylRep_zero_conj_halfTorus m ht

theorem gElt_mem_normalizer (hm : 1 ≤ m) : gElt φ₁ ∈ Subgroup.normalizer (Bs : Set G) :=
  h.mem_normalizer_L fun _ ht => slPerm_sigma_conj_halfTorus m hm ht

theorem sk_mem_normalizer :
    φ₂ (weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩) ∈ Subgroup.normalizer (Bs : Set G) :=
  h.mem_normalizer_K fun _ ht => weylRep_last_conj_halfTorusK m ht

theorem hElt_mem_normalizer (hm : 1 ≤ m) : hElt φ₂ ∈ Subgroup.normalizer (Bs : Set G) :=
  h.mem_normalizer_K fun _ ht => slPerm_tau_conj_halfTorusK m hm ht

end GGHalfCtx

end CFSG.StandardType

end
