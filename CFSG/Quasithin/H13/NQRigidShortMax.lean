module

public import CFSG.Quasithin.H13.NQRigidShortSL2

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup
open scoped MatrixGroups

theorem sylow_max_of_sl2_normal {Γ₀ : Type*} [Group Γ₀] [Finite Γ₀]
    {G₀ L₀ P₀ X : Subgroup Γ₀} (hLG : L₀ ≤ G₀) (hGL : G₀ ≤ normalizer (L₀ : Set Γ₀))
    (hPG : P₀ ≤ G₀) (hP2 : IsPGroup 2 P₀) (hGLP : ∀ g ∈ G₀, ∃ l ∈ L₀, ∃ s ∈ P₀, g = l * s)
    {n : ℕ} {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n)
    [IsSimpleGroup SL(2, F)] (α₀ : ↥L₀ ≃* SL(2, F)) (hXL : X ≤ L₀) (hXP : X ≤ P₀)
    (hX : Nat.card X = 2 ^ n) :
    Nat.card ↥(P₀ ⊓ L₀) = 2 ^ n ∧ ¬ 2 ∣ P₀.relIndex G₀ ∧
      P₀ ≤ normalizer ((P₀ ⊓ L₀ : Subgroup Γ₀) : Set Γ₀) ∧
      ∀ Y : Subgroup Γ₀, P₀ ≤ Y → Y ≤ G₀ → Y ≠ G₀ →
        Y ≤ normalizer ((P₀ ⊓ L₀ : Subgroup Γ₀) : Set Γ₀) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : ∀ Y : Subgroup Γ₀, Y ≤ L₀ → IsPGroup 2 Y → Nat.card Y ∣ 2 ^ n := by
    intro Y hYL hY
    rw [← Nat.card_congr (subgroupOfEquivOfLe hYL).toEquiv]
    exact card_dvd_of_isPGroup_of_sl2 hF α₀ hY.comap_subtype
  have hU2 : IsPGroup 2 ↥(P₀ ⊓ L₀) := hP2.to_le inf_le_left
  have hUcard : Nat.card ↥(P₀ ⊓ L₀) = 2 ^ n := by
    apply le_antisymm (Nat.le_of_dvd (by positivity) (hdvd _ inf_le_right hU2))
    rw [← hX]
    exact card_le_of_le (le_inf hXP hXL)
  have hLcard : Nat.card L₀ = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr α₀.toEquiv]
    exact (card_sl2_two hF).1
  have hsup : L₀.subgroupOf G₀ ⊔ P₀.subgroupOf G₀ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨g, hg⟩ -
    obtain ⟨l, hl, s, hs, hls⟩ := hGLP g hg
    have he : (⟨g, hg⟩ : ↥G₀) = ⟨l, hLG hl⟩ * ⟨s, hPG hs⟩ := Subtype.ext hls
    rw [he]
    exact mul_mem (mem_sup_left (show (⟨l, hLG hl⟩ : ↥G₀) ∈ L₀.subgroupOf G₀ from hl))
      (mem_sup_right (show (⟨s, hPG hs⟩ : ↥G₀) ∈ P₀.subgroupOf G₀ from hs))
  have hLn : (L₀.subgroupOf G₀).Normal := (normal_subgroupOf_iff_le_normalizer hLG).mpr hGL
  have e1 : L₀.relIndex G₀ = L₀.relIndex P₀ := by
    have h := relIndex_sup_left (P₀.subgroupOf G₀) (L₀.subgroupOf G₀)
    rw [hsup, relIndex_top_right, relIndex_subgroupOf hPG] at h
    exact h
  have e2 : L₀.relIndex G₀ * Nat.card L₀ = Nat.card G₀ := by
    have h := relIndex_mul_card L₀ G₀
    rwa [inf_of_le_left hLG] at h
  have e3 : P₀.relIndex G₀ * Nat.card P₀ = Nat.card G₀ := by
    have h := relIndex_mul_card P₀ G₀
    rwa [inf_of_le_left hPG] at h
  have e4 : L₀.relIndex P₀ * 2 ^ n = Nat.card P₀ := by
    have h := relIndex_mul_card L₀ P₀
    rwa [inf_comm, hUcard] at h
  have hpos : 0 < L₀.relIndex P₀ * 2 ^ n := e4 ▸ Nat.card_pos
  have hidx : P₀.relIndex G₀ = (2 ^ n) ^ 2 - 1 := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc P₀.relIndex G₀ * (L₀.relIndex P₀ * 2 ^ n) = Nat.card G₀ := by rw [e4, e3]
      _ = L₀.relIndex G₀ * Nat.card L₀ := e2.symm
      _ = ((2 ^ n) ^ 2 - 1) * (L₀.relIndex P₀ * 2 ^ n) := by rw [e1, hLcard]; ring
  refine ⟨hUcard, fun h => ?_, fun s hs => ?_, ?_⟩
  · rw [hidx] at h
    exact (Nat.not_even_iff_odd.mpr (card_sl2_two hF).2) (even_iff_two_dvd.mpr h)
  · exact inf_normalizer_le_normalizer_inf ⟨le_normalizer hs, hGL (hPG hs)⟩
  intro Y hPY hYG hYne y hy
  have hYL : ¬ L₀ ≤ Y := fun h => hYne (le_antisymm hYG fun g hg => by
    obtain ⟨l, hl, s, hs, rfl⟩ := hGLP g hg
    exact mul_mem (h hl) (hPY hs))
  have hUq : Nat.card ↥(((P₀ ⊓ L₀).subgroupOf L₀).map α₀.toMonoidHom) = 2 ^ n := by
    rw [card_map_of_injective (f := α₀.toMonoidHom) α₀.injective,
      Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv, hUcard]
  have hMq : ((Y ⊓ L₀).subgroupOf L₀).map α₀.toMonoidHom < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hYL fun l hl => ?_
    have h1 : α₀ ⟨l, hl⟩ ∈ ((Y ⊓ L₀).subgroupOf L₀).map α₀.toMonoidHom := h ▸ mem_top _
    obtain ⟨y', hy', he⟩ := h1
    have h2 : y' = ⟨l, hl⟩ := α₀.injective he
    rw [h2] at hy'
    exact (mem_inf.mp hy').1
  have hUM : ((P₀ ⊓ L₀).subgroupOf L₀).map α₀.toMonoidHom ≤
      ((Y ⊓ L₀).subgroupOf L₀).map α₀.toMonoidHom :=
    map_mono fun z hz => ⟨hPY (mem_inf.mp hz).1, (mem_inf.mp hz).2⟩
  have hMN := sl2_le_normalizer_of_lt_top hF hUq hMq hUM
  have hYLN : ∀ z ∈ Y ⊓ L₀, z ∈ normalizer ((P₀ ⊓ L₀ : Subgroup Γ₀) : Set Γ₀) := by
    intro z hz
    have hzL : z ∈ L₀ := (mem_inf.mp hz).2
    have hzq : α₀ ⟨z, hzL⟩ ∈ normalizer
        ((((P₀ ⊓ L₀).subgroupOf L₀).map α₀.toMonoidHom : Subgroup SL(2, F)) : Set SL(2, F)) :=
      hMN ⟨⟨z, hzL⟩, hz, rfl⟩
    rw [← map_equiv_normalizer_eq] at hzq
    obtain ⟨z', hz', he⟩ := mem_map.mp hzq
    have hzz : z' = ⟨z, hzL⟩ := α₀.injective he
    rw [hzz] at hz'
    rw [mem_normalizer_iff] at hz' ⊢
    intro u
    constructor
    · intro hu
      exact (hz' ⟨u, (mem_inf.mp hu).2⟩).mp hu
    · intro hu
      have hul : u ∈ L₀ := by
        have h1 : z * u * z⁻¹ ∈ L₀ := (mem_inf.mp hu).2
        have h2 : u = z⁻¹ * (z * u * z⁻¹) * z := by group
        rw [h2]
        exact mul_mem (mul_mem (inv_mem hzL) h1) hzL
      exact (hz' ⟨u, hul⟩).mpr hu
  have hUy : (P₀ ⊓ L₀).map (MulAut.conj y).toMonoidHom ≤ Y ⊓ L₀ := by
    rintro _ ⟨u, hu, rfl⟩
    show y * u * y⁻¹ ∈ Y ⊓ L₀
    exact mem_inf.mpr ⟨mul_mem (mul_mem hy (hPY (mem_inf.mp hu).1)) (inv_mem hy),
      (mem_normalizer_iff.mp (hGL (hYG hy)) u).mp (mem_inf.mp hu).2⟩
  have hUy2 : IsPGroup 2 ↥((P₀ ⊓ L₀).map (MulAut.conj y).toMonoidHom) := hU2.map _
  have hUyN : (P₀ ⊓ L₀).map (MulAut.conj y).toMonoidHom ≤
      normalizer ((P₀ ⊓ L₀ : Subgroup Γ₀) : Set Γ₀) := fun x hx => hYLN x (hUy hx)
  have hsup2 := hU2.to_sup_of_normal_left' hUy2 hUyN
  have hsupL : (P₀ ⊓ L₀) ⊔ (P₀ ⊓ L₀).map (MulAut.conj y).toMonoidHom ≤ L₀ :=
    sup_le inf_le_right (hUy.trans inf_le_right)
  have hsupeq : P₀ ⊓ L₀ = (P₀ ⊓ L₀) ⊔ (P₀ ⊓ L₀).map (MulAut.conj y).toMonoidHom :=
    eq_of_le_of_card_ge le_sup_left
      (by rw [hUcard]; exact Nat.le_of_dvd (by positivity) (hdvd _ hsupL hsup2))
  have hUyle : (P₀ ⊓ L₀).map (MulAut.conj y).toMonoidHom ≤ P₀ ⊓ L₀ :=
    le_sup_right.trans hsupeq.ge
  have hUyeq : (P₀ ⊓ L₀).map (MulAut.conj y).toMonoidHom = P₀ ⊓ L₀ :=
    eq_of_le_of_card_ge hUyle
      (card_map_of_injective (f := (MulAut.conj y).toMonoidHom) (MulAut.conj y).injective).ge
  rw [mem_normalizer_iff_map_conj_eq]
  exact hUyeq

end CFSG.Quasithin.H13.NQRigid
