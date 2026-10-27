module

public import CFSG.Quasithin.Background.FFC3Data
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.B4L3Coord

public section

namespace CFSG.Quasithin

namespace FFC

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem mem_StatedSL_two {n : ℕ} (g : GL (Fin n) (ZMod 2)) : g ∈ StatedSL n (ZMod 2) :=
  CFSG.Open.StatedAPI.mem_statedSL_zmod_two g

@[expose] def toStated (n : ℕ) : GL (Fin n) (ZMod 2) →* ↥(StatedSL n (ZMod 2)) :=
  (MonoidHom.id (GL (Fin n) (ZMod 2))).codRestrict _ mem_StatedSL_two

theorem toStated_surjective (n : ℕ) : Function.Surjective (toStated n) :=
  fun γ => ⟨γ.1, Subtype.ext rfl⟩

theorem eq_one_of_fixes {n : ℕ} {g : GL (Fin n) (ZMod 2)}
    (h : ∀ x : Fin n → ZMod 2, (g : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec x = x) : g = 1 := by
  apply Units.ext
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using this

theorem eq_zero_of_fixed_nat {m : ℕ} {x : Fin (m + 2) → ZMod 2}
    (h : ∀ g : GL (Fin (m + 2)) (ZMod 2), (g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)).mulVec x = x) :
    x = 0 := by
  funext j
  by_contra hj
  have hj1 : x j = 1 := zmod2_eq_one_of_ne_zero hj
  obtain ⟨k, hk⟩ : ∃ k : Fin (m + 2), k ≠ j := by
    by_cases hj0 : j = 0
    · exact ⟨1, by rw [hj0]; exact Fin.one_eq_zero_iff.not.2 (by omega)⟩
    · exact ⟨0, fun h0 => hj0 h0.symm⟩
  have h1 := congrFun (h (elemTv k j hk)) k
  rw [elemTv_mulVec] at h1
  simp [hj1] at h1

theorem eq_zero_of_fixed_dual {m : ℕ} {w : Fin (m + 2) → ZMod 2}
    (h : ∀ g : GL (Fin (m + 2)) (ZMod 2),
      (((g⁻¹ : GL (Fin (m + 2)) (ZMod 2)) : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))ᵀ).mulVec w = w) :
    w = 0 := by
  funext j
  by_contra hj
  have hj1 : w j = 1 := zmod2_eq_one_of_ne_zero hj
  obtain ⟨k, hk⟩ : ∃ k : Fin (m + 2), k ≠ j := by
    by_cases hj0 : j = 0
    · exact ⟨1, by rw [hj0]; exact Fin.one_eq_zero_iff.not.2 (by omega)⟩
    · exact ⟨0, fun h0 => hj0 h0.symm⟩
  have h1 := congrFun (h (elemTv j k hk.symm)⁻¹) k
  rw [inv_inv, elemTv_transpose_mulVec] at h1
  simp [hj1] at h1

section PairData

variable {V : Type} [CommGroup V] {m : ℕ}

structure PairData (m : ℕ) (ρ : GL (Fin (m + 2)) (ZMod 2) →* MulAut V) (U₁ U₂ : Subgroup V) where
  e₁ : ↥U₁ ≃* MV (m + 2)
  e₂ : ↥U₂ ≃* MV (m + 2)
  inv₁ : ∀ (g : GL (Fin (m + 2)) (ZMod 2)), ∀ u ∈ U₁, ρ g u ∈ U₁
  inv₂ : ∀ (g : GL (Fin (m + 2)) (ZMod 2)), ∀ u ∈ U₂, ρ g u ∈ U₂
  equi₁ : ∀ (g : GL (Fin (m + 2)) (ZMod 2)) (u : ↥U₁) (hu : ρ g (u : V) ∈ U₁),
    e₁ ⟨ρ g (u : V), hu⟩ = actN g (e₁ u)
  equi₂ : ∀ (g : GL (Fin (m + 2)) (ZMod 2)) (u : ↥U₂) (hu : ρ g (u : V) ∈ U₂),
    e₂ ⟨ρ g (u : V), hu⟩ = actD g (e₂ u)

namespace PairData

variable {ρ : GL (Fin (m + 2)) (ZMod 2) →* MulAut V} {U₁ U₂ : Subgroup V} (P : PairData m ρ U₁ U₂)

include P in
theorem act₁ (g : GL (Fin (m + 2)) (ZMod 2)) (x : MV (m + 2)) :
    ρ g ((P.e₁.symm x : ↥U₁) : V) = ((P.e₁.symm (actN g x) : ↥U₁) : V) := by
  have hu : ρ g ((P.e₁.symm x : ↥U₁) : V) ∈ U₁ := P.inv₁ g _ (P.e₁.symm x).2
  have h := P.equi₁ g (P.e₁.symm x) hu
  rw [MulEquiv.apply_symm_apply] at h
  have h2 : (⟨ρ g ((P.e₁.symm x : ↥U₁) : V), hu⟩ : ↥U₁) = P.e₁.symm (actN g x) :=
    (MulEquiv.eq_symm_apply _).2 h
  exact congrArg Subtype.val h2

include P in
theorem act₂ (g : GL (Fin (m + 2)) (ZMod 2)) (x : MV (m + 2)) :
    ρ g ((P.e₂.symm x : ↥U₂) : V) = ((P.e₂.symm (actD g x) : ↥U₂) : V) := by
  have hu : ρ g ((P.e₂.symm x : ↥U₂) : V) ∈ U₂ := P.inv₂ g _ (P.e₂.symm x).2
  have h := P.equi₂ g (P.e₂.symm x) hu
  rw [MulEquiv.apply_symm_apply] at h
  have h2 : (⟨ρ g ((P.e₂.symm x : ↥U₂) : V), hu⟩ : ↥U₂) = P.e₂.symm (actD g x) :=
    (MulEquiv.eq_symm_apply _).2 h
  exact congrArg Subtype.val h2

include P in
theorem ρ_injective : Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply eq_one_of_fixes
  intro y
  have h := P.act₁ g (Multiplicative.ofAdd y)
  rw [hg, MulAut.one_apply] at h
  have h2 := P.e₁.symm.injective (Subtype.ext h)
  have h3 := congrArg Multiplicative.toAdd h2
  exact h3.symm

end PairData

theorem exists_pairData {L : Subgroup (MulAut V)} {U₁ U₂ : Subgroup V}
    {π : ↥(StatedSL (m + 2) (ZMod 2)) →* ↥L}
    (h₁ : (FFModel.nat (StatedSL (m + 2) (ZMod 2))).RealizesVia L U₁ ⊥ π)
    (h₂ : (FFModel.dualNat (StatedSL (m + 2) (ZMod 2))).RealizesVia L U₂ ⊥ π) :
    ∃ ρ : GL (Fin (m + 2)) (ZMod 2) →* MulAut V, ρ.range = L ∧ Nonempty (PairData m ρ U₁ U₂) := by
  let ρ : GL (Fin (m + 2)) (ZMod 2) →* MulAut V := L.subtype.comp (π.comp (toStated (m + 2)))
  have hρg : ∀ g, ρ g = ((π (toStated (m + 2) g) : ↥L) : MulAut V) := fun g => rfl
  refine ⟨ρ, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (π (toStated (m + 2) g)).2
    · intro hx
      obtain ⟨γ, hγ⟩ := h₁.1 ⟨x, hx⟩
      obtain ⟨g, rfl⟩ := toStated_surjective (m + 2) γ
      exact ⟨g, congrArg Subtype.val hγ⟩
  · have hUinv₁ := h₁.2.2.2.1
    have hUinv₂ := h₂.2.2.2.1
    obtain ⟨β₁, hβ₁s, hβ₁k, hβ₁e⟩ := FFModel.RealizesVia.coord (D := FFModel.nat (StatedSL (m + 2) (ZMod 2)))
      rfl rfl h₁
    obtain ⟨β₂, hβ₂s, hβ₂k, hβ₂e⟩ := FFModel.RealizesVia.coord (D := FFModel.dualNat (StatedSL (m + 2) (ZMod 2)))
      rfl rfl h₂
    have hβ₁i : Function.Injective β₁ := by
      rw [injective_iff_map_eq_one]
      intro u hu
      have := (hβ₁k u).1 hu
      exact Subtype.ext (Subgroup.mem_bot.1 this)
    have hβ₂i : Function.Injective β₂ := by
      rw [injective_iff_map_eq_one]
      intro u hu
      have := (hβ₂k u).1 hu
      exact Subtype.ext (Subgroup.mem_bot.1 this)
    refine ⟨⟨MulEquiv.ofBijective β₁ ⟨hβ₁i, hβ₁s⟩, MulEquiv.ofBijective β₂ ⟨hβ₂i, hβ₂s⟩,
      fun g u hu => hUinv₁ (π (toStated (m + 2) g)) u hu,
      fun g u hu => hUinv₂ (π (toStated (m + 2) g)) u hu, ?_, ?_⟩⟩
    · intro g u hu
      exact hβ₁e (toStated (m + 2) g) u hu
    · intro g u hu
      exact hβ₂e (toStated (m + 2) g) u hu

theorem eq_of_mul_eq_of_inf_eq_bot {U₁ U₂ : Subgroup V} (h : U₁ ⊓ U₂ = ⊥) {y y' z z' : V}
    (hy : y ∈ U₁) (hy' : y' ∈ U₁) (hz : z ∈ U₂) (hz' : z' ∈ U₂) (hyz : y * z = y' * z') :
    y = y' ∧ z = z' := by
  have h1 : y'⁻¹ * y = z' * z⁻¹ := by
    have : y'⁻¹ * y * z = z' := by
      calc y'⁻¹ * y * z = y'⁻¹ * (y * z) := by rw [mul_assoc]
        _ = y'⁻¹ * (y' * z') := by rw [hyz]
        _ = z' := by rw [inv_mul_cancel_left]
    rw [eq_mul_inv_iff_mul_eq]
    exact this
  have h2 : y'⁻¹ * y ∈ U₁ ⊓ U₂ :=
    ⟨U₁.mul_mem (U₁.inv_mem hy') hy, h1 ▸ U₂.mul_mem hz' (U₂.inv_mem hz)⟩
  rw [h, Subgroup.mem_bot] at h2
  have hyy : y = y' := by
    calc y = y' * (y'⁻¹ * y) := by rw [mul_inv_cancel_left]
      _ = y' := by rw [h2, mul_one]
  refine ⟨hyy, ?_⟩
  rw [hyy] at hyz
  exact mul_left_cancel hyz

namespace PairData

variable {ρ : GL (Fin (m + 2)) (ZMod 2) →* MulAut V} {U₁ U₂ : Subgroup V} (P : PairData m ρ U₁ U₂)

include P in
theorem eq_one_of_fixed₁ {y : V} (hy : y ∈ U₁) (h : ∀ g, ρ g y = y) : y = 1 := by
  have hx : ∀ g : GL (Fin (m + 2)) (ZMod 2), actN g (P.e₁ ⟨y, hy⟩) = P.e₁ ⟨y, hy⟩ := by
    intro g
    have h1 := P.act₁ g (P.e₁ ⟨y, hy⟩)
    rw [MulEquiv.symm_apply_apply, h g] at h1
    have h2 : (⟨y, hy⟩ : ↥U₁) = P.e₁.symm (actN g (P.e₁ ⟨y, hy⟩)) := Subtype.ext h1
    exact ((MulEquiv.eq_symm_apply _).1 h2).symm
  have h0 := eq_zero_of_fixed_nat (fun g => congrArg Multiplicative.toAdd (hx g))
  have h3 : P.e₁ ⟨y, hy⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    exact h0
  have h4 : (⟨y, hy⟩ : ↥U₁) = 1 := (MulEquiv.map_eq_one_iff P.e₁).1 h3
  exact congrArg Subtype.val h4

include P in
theorem eq_one_of_fixed₂ {z : V} (hz : z ∈ U₂) (h : ∀ g, ρ g z = z) : z = 1 := by
  have hx : ∀ g : GL (Fin (m + 2)) (ZMod 2), actD g (P.e₂ ⟨z, hz⟩) = P.e₂ ⟨z, hz⟩ := by
    intro g
    have h1 := P.act₂ g (P.e₂ ⟨z, hz⟩)
    rw [MulEquiv.symm_apply_apply, h g] at h1
    have h2 : (⟨z, hz⟩ : ↥U₂) = P.e₂.symm (actD g (P.e₂ ⟨z, hz⟩)) := Subtype.ext h1
    exact ((MulEquiv.eq_symm_apply _).1 h2).symm
  have h0 := eq_zero_of_fixed_dual (fun g => congrArg Multiplicative.toAdd (hx g))
  have h3 : P.e₂ ⟨z, hz⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    exact h0
  have h4 : (⟨z, hz⟩ : ↥U₂) = 1 := (MulEquiv.map_eq_one_iff P.e₂).1 h3
  exact congrArg Subtype.val h4

include P in
theorem U₁_ne_bot : U₁ ≠ ⊥ := by
  intro h
  have hx : Multiplicative.ofAdd (Pi.single (0 : Fin (m + 2)) (1 : ZMod 2)) ≠ (1 : MV (m + 2)) := by
    intro h0
    have := congrFun (congrArg Multiplicative.toAdd h0) 0
    simp at this
  apply hx
  have hu : ((P.e₁.symm (Multiplicative.ofAdd (Pi.single (0 : Fin (m + 2)) (1 : ZMod 2))) : ↥U₁) : V) =
      1 := Subgroup.mem_bot.1 (h ▸ (P.e₁.symm _).2)
  have : P.e₁.symm (Multiplicative.ofAdd (Pi.single (0 : Fin (m + 2)) (1 : ZMod 2))) = 1 :=
    Subtype.ext hu
  simpa using congrArg P.e₁ this

include P in
theorem U₂_ne_bot : U₂ ≠ ⊥ := by
  intro h
  have hx : Multiplicative.ofAdd (Pi.single (0 : Fin (m + 2)) (1 : ZMod 2)) ≠ (1 : MV (m + 2)) := by
    intro h0
    have := congrFun (congrArg Multiplicative.toAdd h0) 0
    simp at this
  apply hx
  have hu : ((P.e₂.symm (Multiplicative.ofAdd (Pi.single (0 : Fin (m + 2)) (1 : ZMod 2))) : ↥U₂) : V) =
      1 := Subgroup.mem_bot.1 (h ▸ (P.e₂.symm _).2)
  have : P.e₂.symm (Multiplicative.ofAdd (Pi.single (0 : Fin (m + 2)) (1 : ZMod 2))) = 1 :=
    Subtype.ext hu
  simpa using congrArg P.e₂ this

include P in
theorem fixed_eq_bot {L : Subgroup (MulAut V)} (hL : ρ.range = L) (hU : IsIntDirect U₁ U₂ (commV L)) :
    XMod.fixed ↥L (commV L) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨hcU, hcfix⟩ := hc
  rw [← hU.1] at hcU
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hcU
  have hg : ∀ g : GL (Fin (m + 2)) (ZMod 2), ρ g (y * z) = y * z := by
    intro g
    have hgL : ρ g ∈ L := hL ▸ ⟨g, rfl⟩
    exact hcfix ⟨ρ g, hgL⟩
  have hdec : ∀ g : GL (Fin (m + 2)) (ZMod 2), ρ g y = y ∧ ρ g z = z := by
    intro g
    have h1 := hg g
    rw [map_mul] at h1
    exact eq_of_mul_eq_of_inf_eq_bot hU.2 (P.inv₁ g y hy) hy (P.inv₂ g z hz) hz h1
  have hy1 : y = 1 := P.eq_one_of_fixed₁ hy fun g => (hdec g).1
  have hz1 : z = 1 := P.eq_one_of_fixed₂ hz fun g => (hdec g).2
  rw [hy1, hz1, mul_one]
  exact Subgroup.one_mem _

include P in
theorem not_irrPlus {L : Subgroup (MulAut V)} (hL : ρ.range = L) (hU : IsIntDirect U₁ U₂ (commV L)) :
    commV L ∉ IrrPlus L ⊤ := by
  intro h
  have hirr := h.2.2.2
  have hfix := P.fixed_eq_bot hL hU
  have hU₁ : U₁ ≤ commV L := hU.1 ▸ le_sup_left
  have hinv : XMod.IsInv ↥L U₁ := by
    intro a l hl
    obtain ⟨g, hg⟩ : (a : MulAut V) ∈ ρ.range := hL ▸ a.2
    show (a : MulAut V) l ∈ U₁
    rw [← hg]
    exact P.inv₁ g l hl
  rcases hirr.2 U₁ hinv (hfix ▸ bot_le) hU₁ with h1 | h1
  · rw [hfix] at h1
    exact P.U₁_ne_bot h1
  · have hU₂ : U₂ ≤ U₁ := by
      calc U₂ ≤ commV L := hU.1 ▸ le_sup_right
        _ = U₁ := h1.symm
    have : U₂ ≤ U₁ ⊓ U₂ := le_inf hU₂ le_rfl
    rw [hU.2, le_bot_iff] at this
    exact P.U₂_ne_bot this

@[expose] def mulMap (L : Subgroup (MulAut V)) : MV (m + 2) × (MV (m + 2) × ↥(fixV L)) →* V :=
  (U₁.subtype.comp P.e₁.symm.toMonoidHom).coprod
    ((U₂.subtype.comp P.e₂.symm.toMonoidHom).coprod (fixV L).subtype)

theorem mulMap_apply (L : Subgroup (MulAut V)) (x w : MV (m + 2)) (k : ↥(fixV L)) :
    P.mulMap L (x, w, k) = ((P.e₁.symm x : ↥U₁) : V) * (((P.e₂.symm w : ↥U₂) : V) * (k : V)) := rfl

include P in
theorem mulMap_bijective {L : Subgroup (MulAut V)} (hU : IsIntDirect U₁ U₂ (commV L))
    (hVd : IsIntDirect (commV L) (fixV L) ⊤) : Function.Bijective (P.mulMap L) := by
  constructor
  · rw [injective_iff_map_eq_one]
    rintro ⟨x, w, k⟩ h
    rw [mulMap_apply] at h
    have hak : (((P.e₁.symm x : ↥U₁) : V) * ((P.e₂.symm w : ↥U₂) : V)) * (k : V) = 1 := by
      rw [mul_assoc]
      exact h
    have hmem : ((P.e₁.symm x : ↥U₁) : V) * ((P.e₂.symm w : ↥U₂) : V) ∈ commV L ⊓ fixV L := by
      refine ⟨?_, ?_⟩
      · rw [← hU.1]
        exact Subgroup.mul_mem_sup (P.e₁.symm x).2 (P.e₂.symm w).2
      · have h1 : ((P.e₁.symm x : ↥U₁) : V) * ((P.e₂.symm w : ↥U₂) : V) = (k : V)⁻¹ :=
          eq_inv_of_mul_eq_one_left hak
        rw [h1]
        exact (fixV L).inv_mem k.2
    rw [hVd.2, Subgroup.mem_bot] at hmem
    have hk : (k : V) = 1 := by
      rw [hmem, one_mul] at hak
      exact hak
    have hk' : k = 1 := Subtype.ext hk
    have h2 := eq_of_mul_eq_of_inf_eq_bot hU.2 (P.e₁.symm x).2 (U₁.one_mem) (P.e₂.symm w).2
      (U₂.one_mem) (by rw [hmem, mul_one])
    have hx : P.e₁.symm x = 1 := Subtype.ext h2.1
    have hw : P.e₂.symm w = 1 := Subtype.ext h2.2
    have hx' : x = 1 := by simpa using congrArg P.e₁ hx
    have hw' : w = 1 := by simpa using congrArg P.e₂ hw
    rw [hx', hw', hk']
    rfl
  · intro v
    have hv : v ∈ commV L ⊔ fixV L := by rw [hVd.1]; exact Subgroup.mem_top v
    obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 hv
    rw [← hU.1] at hu
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hu
    refine ⟨(P.e₁ ⟨y, hy⟩, P.e₂ ⟨z, hz⟩, ⟨c, hc⟩), ?_⟩
    rw [mulMap_apply]
    simp [mul_assoc]

include P in
theorem mulMap_equi {L : Subgroup (MulAut V)} (hL : ρ.range = L) (g : GL (Fin (m + 2)) (ZMod 2))
    (x w : MV (m + 2)) (k : ↥(fixV L)) :
    ρ g (P.mulMap L (x, w, k)) = P.mulMap L (actN g x, actD g w, k) := by
  rw [mulMap_apply, mulMap_apply, map_mul, map_mul, P.act₁, P.act₂]
  have hgL : ρ g ∈ L := hL ▸ ⟨g, rfl⟩
  rw [k.2 (ρ g) hgL]

@[expose] noncomputable def toSumDualData {L : Subgroup (MulAut V)} (hL : ρ.range = L)
    (hU : IsIntDirect U₁ U₂ (commV L)) (hVd : IsIntDirect (commV L) (fixV L) ⊤) :
    SumDualData m ρ (fixV L) where
  Θ := (MulEquiv.ofBijective (P.mulMap L) (P.mulMap_bijective hU hVd)).symm
  equi g v := by
    let μ := MulEquiv.ofBijective (P.mulMap L) (P.mulMap_bijective hU hVd)
    have hμ : ∀ t, μ t = P.mulMap L t := fun t => rfl
    have hv : v = μ (μ.symm v) := (μ.apply_symm_apply v).symm
    show μ.symm (ρ g v) = (actN g (μ.symm v).1, actD g (μ.symm v).2.1, (μ.symm v).2.2)
    rw [MulEquiv.symm_apply_eq]
    rw [hμ]
    conv_lhs => rw [hv, hμ]
    exact P.mulMap_equi hL g _ _ _

end PairData

end PairData

theorem part6_aux {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)}
    (h4 : B51Part4 L L) (n : ℕ) (hn : SumNatDual L (commV L) n) (T : Subgroup (MulAut V))
    (hT : IsSylowTwoOf T L) :
    (∃ R : Subgroup (MulAut V), R ≤ L ⊓ centSub (fixV T) ∧ IsPGroup 2 R ∧
        Nat.card R = 2 ^ (1 + 2 * (n - 2)) ∧
        ∃ _ : (R.subgroupOf (L ⊓ centSub (fixV T))).Normal,
          Nonempty (↥(L ⊓ centSub (fixV T)) ⧸ R.subgroupOf (L ⊓ centSub (fixV T)) ≃*
            Matrix.GeneralLinearGroup (Fin (n - 2)) (ZMod 2))) ∧
      ∀ A, IsFFStarOffender L A → ¬ A ≤ pCoreOf 2 (L ⊓ centSub (fixV T)) := by
  obtain ⟨hn45, π, U₁, U₂, hU, h₁, h₂⟩ := hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨ρ, hρL, ⟨P⟩⟩ := exists_pairData h₁ h₂
  have hVd : IsIntDirect (commV L) (fixV L) ⊤ := by
    by_contra hnd
    exact P.not_irrPlus hρL hU (h4 hnd).1
  exact (P.toSumDualData hρL hU hVd).sylow_part6 P.ρ_injective hρL hT

theorem part6_of_part4 {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}
    (h4 : B51Part4 G L) : B51Part6 G L := by
  intro n hn T hT
  obtain ⟨hGL, hn⟩ := hn
  subst hGL
  exact part6_aux h4 n hn T hT

end FFC

end CFSG.Quasithin
