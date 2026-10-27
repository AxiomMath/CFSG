module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeTriple

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType

@[expose] def zT {G : Type} [Group G] (g : Fin 3 → G) (x : G) (i : Fin 3) : G := g i * x * (g i)⁻¹

@[expose] def LT {G : Type} [Group G] (g : Fin 3 → G) (L : Subgroup G) (i : Fin 3) : Subgroup G :=
  L.map (MulAut.conj (g i)).toMonoidHom

theorem mem_LT {G : Type} [Group G] {g : Fin 3 → G} {L : Subgroup G} {i : Fin 3} {y : G} :
    y ∈ LT g L i ↔ (g i)⁻¹ * y * g i ∈ L := by
  rw [LT, mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem conj_mem_cent_iff {G : Type} [Group G] {g b : G} {S : Subgroup G} :
    b ∈ centralizer (S.map (MulAut.conj g).toMonoidHom : Set G) ↔
      g⁻¹ * b * g ∈ centralizer (S : Set G) := by
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hb s hs
    have := hb (g * s * g⁻¹) (by
      rw [SetLike.mem_coe, mem_map_equiv]
      simp only [MulAut.conj_symm_apply]
      rw [show g⁻¹ * (g * s * g⁻¹) * g = s by group]; exact hs)
    calc s * (g⁻¹ * b * g) = g⁻¹ * ((g * s * g⁻¹) * b) * g := by group
      _ = g⁻¹ * (b * (g * s * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * b * g * s := by group
  · intro hb t ht
    rw [SetLike.mem_coe, mem_map_equiv] at ht
    have := hb _ (by simpa [MulAut.conj_symm_apply] using ht)
    calc t * b = g * ((g⁻¹ * t * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * t * g)) * g⁻¹ := by rw [this]
      _ = b * t := by group

theorem conj_mem_cent_single_iff {G : Type} [Group G] {g b z : G} :
    b ∈ centralizer ({g * z * g⁻¹} : Set G) ↔ g⁻¹ * b * g ∈ centralizer ({z} : Set G) := by
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * b * g * z = g⁻¹ * (b * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * b) * g := by rw [h]
      _ = z * (g⁻¹ * b * g) := by group
  · intro h
    calc b * (g * z * g⁻¹) = g * ((g⁻¹ * b * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * b * g)) * g⁻¹ := by rw [h]
      _ = g * z * g⁻¹ * b := by group

theorem conj_mem_norm_iff {G : Type} [Group G] {g b : G} {S : Subgroup G} :
    b ∈ normalizer (S.map (MulAut.conj g).toMonoidHom : Set G) ↔
      g⁻¹ * b * g ∈ normalizer (S : Set G) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  have hm : ∀ y, y ∈ S.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ S := fun y => by
    rw [mem_map_equiv]; simp [MulAut.conj_symm_apply]
  constructor
  · intro hb s
    have := hb (g * s * g⁻¹)
    rw [hm, hm] at this
    have e1 : g⁻¹ * (g * s * g⁻¹) * g = s := by group
    have e2 : g⁻¹ * (b * (g * s * g⁻¹) * b⁻¹) * g = g⁻¹ * b * g * s * (g⁻¹ * b * g)⁻¹ := by group
    rw [e1, e2] at this
    exact this
  · intro hb t
    rw [hm, hm]
    have := hb (g⁻¹ * t * g)
    have e2 : g⁻¹ * b * g * (g⁻¹ * t * g) * (g⁻¹ * b * g)⁻¹ = g⁻¹ * (b * t * b⁻¹) * g := by group
    rw [e2] at this
    exact this

@[expose] def bconj {G : Type} [Group G]
    {B : Subgroup G} {g : G} (hg : g ∈ normalizer (B : Set G)) : B →* B where
  toFun b := ⟨g⁻¹ * b * g, by
    have := (mem_normalizer_iff.1 (inv_mem hg) b).1 b.2
    simpa using this⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [MulMemClass.coe_mul]; group)

structure O1pAt {G : Type} [Group G] [Finite G]
    (B Bs : Subgroup G) (x : G) (L T : Subgroup G) (g : Fin 3 → G)
    (χ0 : B →* Multiplicative (ZMod 3)) (X Xk : Subgroup G) : Prop where
  hyp : GGThmIHyp 3 B x L
  bstar : GGBstar 3 B Bs
  Bs_card : Nat.card Bs = 3 ^ 6
  Bs_norm : Bs ≤ normalizer (T : Set G)
  g0 : g 0 = 1
  g_norm : ∀ i, g i ∈ normalizer (B : Set G)
  coord : ∀ i j (hb : (g j)⁻¹ * zT g x i * g j ∈ B), χ0 ⟨_, hb⟩ = if i = j then 1 else ω3
  L_norm : centralizer ({x} : Set G) ≤ normalizer (L : Set G)
  T_card : Nat.card T = 4
  T_cent : L ≤ centralizer (T : Set G)
  T_char : normalizer (L : Set G) ≤ normalizer (T : Set G)
  lemma81 : ∀ b (hb : b ∈ B), b ∈ centralizer (T : Set G) ↔ χ0 ⟨b, hb⟩ = 1
  X_model : LieModel X .PSU 5 2 1
  X_le : X ≤ L ⊓ centralizer ({zT g x 1} : Set G)
  X_split : ∀ h ∈ L ⊓ centralizer ({zT g x 1} : Set G),
    ∃ c ∈ L ⊓ centralizer (L : Set G), ∃ y ∈ X, h = c * y
  X_le_L1 : X ≤ LT g L 1
  B_cent_X : B ⊓ centralizer (X : Set G) = closure {x, x * (zT g x 1)⁻¹}
  Xk_model : LieModel Xk .PSU 4 2 1
  Xk_le : Xk ≤ X ⊓ centralizer ({zT g x 2} : Set G)
  Xk_le_L2 : Xk ≤ LT g L 2
  F14 : ∀ α : MulAut X, (∀ y : X, (y : G) ∈ Xk → α y = y) → α ^ 3 = 1

namespace O1pAt

@[expose] def chi {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L T : Subgroup G}
    {g : Fin 3 → G} {χ0 : B →* Multiplicative (ZMod 3)} {X Xk : Subgroup G}
    (h : O1pAt B Bs x L T g χ0 X Xk)
    (j : Fin 3) : B →* Multiplicative (ZMod 3) := χ0.comp (bconj (h.g_norm j))

theorem z0 {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L T : Subgroup G}
    {g : Fin 3 → G} {χ0 : B →* Multiplicative (ZMod 3)} {X Xk : Subgroup G}
    (h : O1pAt B Bs x L T g χ0 X Xk) : zT g x 0 = x := by simp [zT, h.g0]

theorem L0 {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L T : Subgroup G}
    {g : Fin 3 → G} {χ0 : B →* Multiplicative (ZMod 3)} {X Xk : Subgroup G}
    (h : O1pAt B Bs x L T g χ0 X Xk) (S : Subgroup G) : LT g S 0 = S := by
  ext y; rw [mem_LT, h.g0]; simp

theorem z_mem {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L T : Subgroup G}
    {g : Fin 3 → G} {χ0 : B →* Multiplicative (ZMod 3)} {X Xk : Subgroup G}
    (h : O1pAt B Bs x L T g χ0 X Xk) (i : Fin 3) : zT g x i ∈ B := by
  have hx : x ∈ B := (ggThmIHyp_unpack h.hyp).2.1
  exact (mem_normalizer_iff.1 (h.g_norm i) x).1 hx

theorem toTriple {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L T : Subgroup G}
    {g : Fin 3 → G} {χ0 : B →* Multiplicative (ZMod 3)} {X Xk : Subgroup G}
    (h : O1pAt B Bs x L T g χ0 X Xk) : O1pTriple B Bs (zT g x) (LT g L) (LT g T) h.chi X Xk where
  hyp := by rw [h.z0, h.L0]; exact h.hyp
  bstar := h.bstar
  Bs_card := h.Bs_card
  Bs_norm := by rw [h.L0]; exact h.Bs_norm
  z_mem := h.z_mem
  χ_z i j := h.coord i j _
  Lc_norm i := fun b hb => by
    rw [LT, conj_mem_norm_iff]
    apply h.L_norm
    rw [zT, conj_mem_cent_single_iff] at hb
    exact hb
  T_card i := by
    rw [LT, card_map_of_injective (MulEquiv.injective _)]; exact h.T_card
  T_cent i := fun y hy => by
    rw [LT, conj_mem_cent_iff]
    exact h.T_cent ((mem_LT).1 hy)
  T_char i := fun b hb => by
    rw [LT, conj_mem_norm_iff]
    exact h.T_char ((conj_mem_norm_iff).1 hb)
  lemma81 i b hb := by
    rw [LT, conj_mem_cent_iff]
    exact h.lemma81 _ _
  X_model := h.X_model
  X_le := by rw [h.L0]; exact h.X_le
  X_split := by rw [h.L0]; exact h.X_split
  X_le_L1 := h.X_le_L1
  B_cent_X := by rw [h.z0]; exact h.B_cent_X
  Xk_model := h.Xk_model
  Xk_le := h.Xk_le
  Xk_le_L2 := h.Xk_le_L2
  F14 := h.F14

end O1pAt

theorem o1p_at_false {G : Type} [Group G] [Finite G] (hL : GGLBalanceInput) (hI : PumpUpLieInputs)
    {B Bs : Subgroup G} {x : G} {L T : Subgroup G} {g : Fin 3 → G}
    {χ0 : B →* Multiplicative (ZMod 3)} {X Xk : Subgroup G}
    (h : O1pAt B Bs x L T g χ0 X Xk) : False :=
  o1p_triple_false hL hI h.toTriple

end CFSG.GGQ2Prime
