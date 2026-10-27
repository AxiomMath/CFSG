module

public import CFSG.Quasithin.Background.D2Decomp

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {V : Type*} [CommGroup V]

section Conj

theorem mem_fixV_conjBy {g : MulAut V} {A : Subgroup (MulAut V)} {v : V} :
    v ∈ fixV (conjBy g A) ↔ g⁻¹ v ∈ fixV A := by
  constructor
  · intro h y hy
    have h1 : (g * y * g⁻¹) v = v := h _ (mem_conjBy_of_mem hy)
    have : y (g⁻¹ v) = g⁻¹ v := by
      have h2 : g (y (g⁻¹ v)) = v := h1
      have h3 := congrArg (fun u => g⁻¹ u) h2
      simpa using h3
    exact this
  · intro h x hx
    have h1 := mem_conjBy_iff.mp hx
    have h2 : (g⁻¹ * x * g) (g⁻¹ v) = g⁻¹ v := h _ h1
    have h3 : g⁻¹ (x v) = g⁻¹ v := by simpa using h2
    exact g⁻¹.injective h3

theorem fixV_conjBy (g : MulAut V) (A : Subgroup (MulAut V)) :
    fixV (conjBy g A) = (fixV A).map (g : V ≃* V).toMonoidHom := by
  ext v
  rw [mem_fixV_conjBy]
  constructor
  · intro h
    exact ⟨g⁻¹ v, h, by simp⟩
  · rintro ⟨u, hu, rfl⟩
    simpa using hu

theorem rkIdx_fixV_conjBy (g : MulAut V) (A : Subgroup (MulAut V)) :
    rkIdx (fixV (conjBy g A)) = rkIdx (fixV A) := by
  unfold rkIdx
  rw [fixV_conjBy]
  have := Subgroup.index_map_equiv (H := fixV A) (g : V ≃* V)
  rw [show ((g : V ≃* V).toMonoidHom) = ((g : V ≃* V) : V →* V) from rfl, this]

theorem rk_conjBy (g : MulAut V) (A : Subgroup (MulAut V)) : rk (conjBy g A) = rk A := by
  unfold rk
  rw [card_conjBy]

theorem rAV_conjBy (g : MulAut V) (A : Subgroup (MulAut V)) : rAV (conjBy g A) = rAV A := by
  unfold rAV
  rw [rkIdx_fixV_conjBy, rk_conjBy]

theorem commSub_conjBy (g : MulAut V) (W : Subgroup V) (A : Subgroup (MulAut V)) :
    commSub (W.map g.toMonoidHom) (conjBy g A) = (commSub W A).map g.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x, hx, _, ⟨w, hw, rfl⟩, rfl⟩
    have h1 := mem_conjBy_iff.mp hx
    refine ⟨(g⁻¹ * x * g) w * w⁻¹, ⟨_, h1, w, hw, rfl⟩, ?_⟩
    simp [map_mul, map_inv, mul_assoc]
  · rintro ⟨_, ⟨y, hy, w, hw, rfl⟩, rfl⟩
    refine ⟨g * y * g⁻¹, mem_conjBy_of_mem hy, g w, ⟨w, hw, rfl⟩, ?_⟩
    simp [map_mul, map_inv, mul_assoc]

theorem map_top_toMonoidHom (g : MulAut V) : (⊤ : Subgroup V).map g.toMonoidHom = ⊤ := by
  rw [Subgroup.map_top]
  exact MonoidHom.range_eq_top.mpr g.surjective

theorem commIter_conjBy (g : MulAut V) (A : Subgroup (MulAut V)) (k : ℕ) :
    commIter ⊤ (conjBy g A) k = (commIter ⊤ A k).map g.toMonoidHom := by
  induction k with
  | zero => exact (map_top_toMonoidHom g).symm
  | succ k ih =>
    show commSub (commIter ⊤ (conjBy g A) k) (conjBy g A) =
      (commSub (commIter ⊤ A k) A).map g.toMonoidHom
    rw [ih, commSub_conjBy]

theorem commSeries_conjBy_eq_bot_iff (g : MulAut V) (A : Subgroup (MulAut V)) (k : ℕ) :
    commSeries (conjBy g A) k = ⊥ ↔ commSeries A k = ⊥ := by
  unfold commSeries
  rw [commIter_conjBy]
  exact Subgroup.map_eq_bot_iff_of_injective _ g.injective

theorem IsA2.conjBy {X A : Subgroup (MulAut V)} (h : IsA2 X A) {g : MulAut V} (hg : g ∈ X) :
    IsA2 X (conjBy g A) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact X.mul_mem (X.mul_mem hg (h.le hy)) (X.inv_mem hg)
  · intro hbot
    apply h.ne_bot
    have := card_conjBy g A
    rw [hbot, Subgroup.card_bot] at this
    exact Subgroup.eq_bot_of_card_eq A this.symm
  · intro x hx y hy
    have ha := mem_conjBy_iff.mp hx
    have hb := mem_conjBy_iff.mp hy
    have h1 := h.isElemAbelian2.1 _ ha _ hb
    have h2 : g⁻¹ * (x * y) * g = g⁻¹ * (y * x) * g := by
      calc g⁻¹ * (x * y) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) := by group
        _ = (g⁻¹ * y * g) * (g⁻¹ * x * g) := h1
        _ = g⁻¹ * (y * x) * g := by group
    exact mul_left_cancel (mul_right_cancel h2)
  · intro x hx
    have ha := mem_conjBy_iff.mp hx
    have h1 := h.isElemAbelian2.2 _ ha
    have h2 : g⁻¹ * (x * x) * g = 1 := by
      calc g⁻¹ * (x * x) * g = (g⁻¹ * x * g) * (g⁻¹ * x * g) := by group
        _ = (g⁻¹ * x * g) ^ 2 := (pow_two _).symm
        _ = 1 := h1
    calc x ^ 2 = x * x := pow_two x
      _ = g * (g⁻¹ * (x * x) * g) * g⁻¹ := by group
      _ = 1 := by rw [h2]; group

theorem conjBy_mem_kRle {X A : Subgroup (MulAut V)} {k : ℕ} {r : ℚ} (hA : A ∈ kRle X k r)
    {g : MulAut V} (hg : g ∈ X) : conjBy g A ∈ kRle X k r :=
  ⟨⟨hA.1.1.conjBy hg, by rw [rAV_conjBy]; exact hA.1.2⟩,
    (commSeries_conjBy_eq_bot_iff g A k).mpr hA.2⟩

theorem QhatStar_le [Finite V] {X A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X) : A ≤ X := by
  obtain ⟨r, -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  exact hA2.le

theorem conjBy_mem_QhatStar [Finite V] {X A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X)
    {g : MulAut V} (hg : g ∈ X) : conjBy g A ∈ QhatStar X := by
  obtain ⟨r, hr, hr2, hAk, hmin⟩ := hA
  refine ⟨r, hr, hr2, conjBy_mem_kRle hAk hg, fun B hB hBA => ?_⟩
  have hB' : conjBy g⁻¹ B ∈ kRle X 3 r := conjBy_mem_kRle hB (X.inv_mem hg)
  have hle : conjBy g⁻¹ B ≤ A := by
    have := conjBy_mono (g := g⁻¹) hBA
    rwa [conjBy_conjBy, inv_mul_cancel, conjBy_one] at this
  have heq := hmin _ hB' hle
  have := congrArg (conjBy g) heq
  rwa [conjBy_conjBy, mul_inv_cancel, conjBy_one] at this

end Conj

section Sylow

theorem exists_sylow_of_mem_sylow2Of {X A : Subgroup (MulAut V)} (hA : A ∈ sylow2Of X) :
    ∃ P : Sylow 2 ↥X, (P : Subgroup ↥X) = A.subgroupOf X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAX, hApg, hidx⟩ := hA
  have hpg : IsPGroup 2 ↥(A.subgroupOf X) := hApg.of_equiv (Subgroup.subgroupOfEquivOfLe hAX).symm
  exact ⟨hpg.toSylow hidx, rfl⟩

variable [Finite V]

theorem qhatStar_eq_sylow2Of {X : Subgroup (MulAut V)} (hne : (QhatStar X).Nonempty)
    (hsyl : QhatStar X ⊆ sylow2Of X) : QhatStar X = sylow2Of X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Set.Subset.antisymm hsyl fun S hS => ?_
  obtain ⟨B, hB⟩ := hne
  obtain ⟨P₁, hP₁⟩ := exists_sylow_of_mem_sylow2Of (hsyl hB)
  obtain ⟨P₂, hP₂⟩ := exists_sylow_of_mem_sylow2Of hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥X) P₁ P₂
  have hgS : (g • P₁ : Sylow 2 ↥X) = P₂ := hg
  have h1 : ((g • P₁ : Sylow 2 ↥X) : Subgroup ↥X) = (P₁ : Subgroup ↥X).map (MulAut.conj g).toMonoidHom :=
    rfl
  have hS' : S = conjBy (g : MulAut V) B := by
    have h2 : (S.subgroupOf X) = ((B.subgroupOf X).map (MulAut.conj g).toMonoidHom) := by
      rw [← hP₂, ← hgS, h1, hP₁]
    ext x
    constructor
    · intro hx
      have hxX : x ∈ X := hS.1 hx
      have : (⟨x, hxX⟩ : ↥X) ∈ S.subgroupOf X := hx
      rw [h2] at this
      obtain ⟨y, hy, hyx⟩ := this
      refine ⟨(y : MulAut V), hy, ?_⟩
      have := congrArg Subtype.val hyx
      simpa [MulAut.conj_apply] using this
    · rintro ⟨y, hy, rfl⟩
      have hyX : y ∈ X := (QhatStar_le hB) hy
      have : (⟨y, hyX⟩ : ↥X) ∈ B.subgroupOf X := hy
      have h3 : (MulAut.conj g) ⟨y, hyX⟩ ∈ S.subgroupOf X := by
        rw [h2]; exact ⟨_, this, rfl⟩
      exact h3
  rw [hS']
  exact conjBy_mem_QhatStar hB g.2

theorem mem_sylow2Of_of_card {X B : Subgroup (MulAut V)} (hBX : B ≤ X) (hB : IsPGroup 2 B)
    {m : ℕ} (hm : Odd m) (hcard : Nat.card X = Nat.card B * m) : B ∈ sylow2Of X := by
  refine ⟨hBX, hB, ?_⟩
  have h1 := (B.subgroupOf X).card_mul_index
  have h2 : Nat.card (B.subgroupOf X) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv
  rw [h2, hcard] at h1
  have hpos : 0 < Nat.card B := Nat.card_pos
  have : (B.subgroupOf X).index = m := Nat.eq_of_mul_eq_mul_left hpos h1
  rw [this]
  exact Nat.not_even_iff_odd.mpr hm |> fun h => by
    intro hd
    exact h (even_iff_two_dvd.mpr hd)

end Sylow

end CFSG.Quasithin
