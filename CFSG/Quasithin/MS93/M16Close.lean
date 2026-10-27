module

public import CFSG.Quasithin.MS93.M16Ind
public import CFSG.Quasithin.MS93.S4AH1

public section

namespace CFSG.Quasithin.MS93.M16

open CFSG.Quasithin Matrix

variable {F : Type} [Field F] {V : Type*} [CommGroup V]

theorem submoduleClosure_bot (ρ : SL3 F →* MulAut V) :
    G6.submoduleClosure ρ.range (⊥ : Subgroup V) = ⊥ := by
  refine le_bot_iff.mp (iSup₂_le fun _ _ => ?_)
  rw [Subgroup.map_bot]

theorem rootElt021_ne_one : rootElt 0 2 (1 : F) ≠ 1 := by
  rw [Ne, rootElt_eq_one_iff (by decide)]
  exact one_ne_zero

section Close

variable [CharP F 2] [Finite F] {ρ : SL3 F →* MulAut V}
  (β : ↥(commV ρ.range) ≃* Multiplicative (Fin 3 → F))
  (hβ : ∀ (g : SL3 F) (v w : ↥(commV ρ.range)), (w : V) = ρ g v →
    Multiplicative.toAdd (β w) =
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β v))
include hβ

omit [CharP F 2] [Finite F] in
theorem symm_mulVec (g : SL3 F) (z : Fin 3 → F) :
    ((β.symm (Multiplicative.ofAdd (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ z)) :
      ↥(commV ρ.range)) : V) = ρ g (β.symm (Multiplicative.ofAdd z)) := by
  set v := β.symm (Multiplicative.ofAdd z) with hv
  set w : ↥(commV ρ.range) := ⟨ρ g v, rho_mem_commV ρ g v.2⟩ with hw
  have h := hβ g v w rfl
  rw [hv, MulEquiv.apply_symm_apply, toAdd_ofAdd] at h
  have : w = β.symm (Multiplicative.ofAdd (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ z)) := by
    rw [MulEquiv.eq_symm_apply, ← h, ofAdd_toAdd]
  rw [← this]

variable (hfixV : fixV ρ.range = ⊥)
include hfixV

theorem mem_commV_of_fix {t : SL3 F} (ht : t * t = 1) (ht1 : t ≠ 1) {v : V} (hv : ρ t v = v) :
    v ∈ commV ρ.range := by
  let c : SL3 F → ↥(commV ρ.range) := fun g => ⟨ρ g v * v⁻¹, comm_mem_commV ρ g v⟩
  let f : SL3 F → (Fin 3 → F) := fun g => Multiplicative.toAdd (β (c g))
  have hc : ∀ g k, c (g * k) = ⟨ρ g (c k), rho_mem_commV ρ g (c k).2⟩ * c g := fun g k =>
    Subtype.ext (by
      change ρ (g * k) v * v⁻¹ = ρ g (ρ k v * v⁻¹) * (ρ g v * v⁻¹)
      rw [rho_mul, map_mul (ρ g), map_inv (ρ g)]
      group)
  have hf : S4A.IsCocycle3 f := by
    intro g k
    change Multiplicative.toAdd (β (c (g * k))) = _
    rw [hc, map_mul, toAdd_mul, hβ g (c k) _ rfl, add_comm]
  have hft : f t = 0 := by
    change Multiplicative.toAdd (β (c t)) = 0
    have : c t = 1 := Subtype.ext (by change ρ t v * v⁻¹ = 1; rw [hv, mul_inv_cancel])
    rw [this, map_one, toAdd_one]
  obtain ⟨n, hn⟩ := S4A.exists_coboundary hf ht ht1 hft
  set c₀ := β.symm (Multiplicative.ofAdd n) with hc₀
  have hfix : v * (c₀ : V)⁻¹ ∈ fixV ρ.range := by
    rw [mem_fixV_range]
    intro g
    have h1 : c g = ⟨ρ g c₀, rho_mem_commV ρ g c₀.2⟩ * c₀⁻¹ := by
      apply β.injective
      apply Multiplicative.toAdd.injective
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv,
        hβ g c₀ ⟨ρ g c₀, rho_mem_commV ρ g c₀.2⟩ rfl, hc₀, MulEquiv.apply_symm_apply,
        toAdd_ofAdd]
      change f g = _
      rw [hn, sub_eq_add_neg]
    have h2 := congrArg Subtype.val h1
    change ρ g v * v⁻¹ = ρ g c₀ * (c₀ : V)⁻¹ at h2
    rw [map_mul, map_inv]
    calc ρ g v * (ρ g c₀)⁻¹ = (ρ g v * v⁻¹) * v * (ρ g c₀)⁻¹ := by group
      _ = (ρ g c₀ * (c₀ : V)⁻¹) * v * (ρ g c₀)⁻¹ := by rw [h2]
      _ = v * (c₀ : V)⁻¹ := by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
  rw [hfixV, Subgroup.mem_bot, mul_inv_eq_one] at hfix
  rw [hfix]
  exact c₀.2

omit hfixV [CharP F 2] [Finite F] in
theorem point_mem_of_invariant {D : Subgroup V} (hDC : D ≤ commV ρ.range) (hD : D ≠ ⊥)
    (hDK : ∀ k ∈ (ptStab : Subgroup (SL3 F)), ∀ d ∈ D, ρ k d ∈ D) (a : F) :
    ((β.symm (Multiplicative.ofAdd (a • ![1, 0, 0])) : ↥(commV ρ.range)) : V) ∈ D := by
  let S : AddSubgroup (Fin 3 → F) :=
    { carrier := {y | ((β.symm (Multiplicative.ofAdd y) : ↥(commV ρ.range)) : V) ∈ D}
      add_mem' := fun {x y} hx hy => by
        change ((β.symm (Multiplicative.ofAdd (x + y)) : ↥(commV ρ.range)) : V) ∈ D
        rw [ofAdd_add, map_mul, Subgroup.coe_mul]
        exact D.mul_mem hx hy
      zero_mem' := by
        change ((β.symm (Multiplicative.ofAdd 0) : ↥(commV ρ.range)) : V) ∈ D
        rw [ofAdd_zero, map_one]
        exact D.one_mem
      neg_mem' := fun {x} hx => by
        change ((β.symm (Multiplicative.ofAdd (-x)) : ↥(commV ρ.range)) : V) ∈ D
        rw [ofAdd_neg, map_inv, Subgroup.coe_inv]
        exact D.inv_mem hx }
  have hS : ∀ g ∈ (ptLevi : Subgroup (SL3 F)), ∀ x ∈ S,
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ S := by
    intro g hg x hx
    change ((β.symm (Multiplicative.ofAdd _) : ↥(commV ρ.range)) : V) ∈ D
    rw [symm_mulVec β hβ]
    exact hDK g (ptLevi_le_ptStab hg) _ hx
  obtain ⟨⟨d, hdD⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD
  set y := Multiplicative.toAdd (β ⟨d, hDC hdD⟩) with hy
  have hyS : y ∈ S := by
    change ((β.symm (Multiplicative.ofAdd y) : ↥(commV ρ.range)) : V) ∈ D
    rw [hy, ofAdd_toAdd, MulEquiv.symm_apply_apply]
    exact hdD
  have hy0 : y ≠ 0 := by
    intro h
    apply hd1
    apply Subtype.ext
    have : (⟨d, hDC hdD⟩ : ↥(commV ρ.range)) = 1 := by
      apply β.injective
      rw [map_one]
      apply Multiplicative.toAdd.injective
      rw [← hy, h, toAdd_one]
    exact congrArg (fun x : ↥(commV ρ.range) => (x : V)) this
  by_cases ha : a = 0
  · rw [ha, zero_smul, ofAdd_zero, map_one]
    exact D.one_mem
  rcases ptLevi_invariant_cases S hS with h | h
  · have hy' := eq_smul_e0_of_mem_pt0 (h y hyS)
    have hy00 : y 0 ≠ 0 := fun h0 => hy0 (by rw [hy', h0, zero_smul])
    set t := a * (y 0)⁻¹ with ht
    have ht0 : t ≠ 0 := mul_ne_zero ha (inv_ne_zero hy00)
    have key : a • ![1, 0, 0] =
        ((tor t 1 ht0 one_ne_zero : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y := by
      rw [hy', Matrix.mulVec_smul, tor_mulVec_e0, smul_smul, ht]
      congr 1
      field_simp
    change ((β.symm (Multiplicative.ofAdd (a • ![1, 0, 0])) : ↥(commV ρ.range)) : V) ∈ D
    rw [key, symm_mulVec β hβ]
    exact hDK _ (tor_mem_ptStab _ _ _ _) _ hyS
  · exact h _

theorem commV_le_wOff {W₀ : Subgroup V}
    (hW₀ : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ w ∈ W₀, ρ g w ∈ W₀)
    (hgen : G6.submoduleClosure ρ.range W₀ = ⊤) (hVne : (⊤ : Subgroup V) ≠ ⊥) :
    commV ρ.range ≤ wOff ρ W₀ := by
  set D := W₀ ⊓ commV ρ.range with hDdef
  have hDK : ∀ k ∈ (ptStab : Subgroup (SL3 F)), ∀ d ∈ D, ρ k d ∈ D := fun k hk d hd =>
    ⟨hW₀ k hk d hd.1, rho_mem_commV ρ k hd.2⟩
  have hDne : D ≠ ⊥ := by
    intro hD
    have hK : ∀ k ∈ (ptStab : Subgroup (SL3 F)), ∀ w ∈ W₀, ρ k w = w := fun k hk w hw => by
      have h : ρ k w * w⁻¹ ∈ D :=
        ⟨W₀.mul_mem (hW₀ k hk w hw) (W₀.inv_mem hw), comm_mem_commV ρ k w⟩
      rw [hD, Subgroup.mem_bot, mul_inv_eq_one] at h
      exact h
    have hW₀bot : W₀ = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      have hwC := mem_commV_of_fix β hβ hfixV (rootElt_mul_self 0 2 1) rootElt021_ne_one
        (hK _ (rootElt_mem_ptStab (by decide) 1) w hw)
      have : w ∈ D := ⟨hw, hwC⟩
      rwa [hD] at this
    apply hVne
    rw [← hgen, hW₀bot, submoduleClosure_bot]
  have hPx : ∀ x : Fin 3 → F, x 2 ≠ 0 → ∀ a : F,
      ((β.symm (Multiplicative.ofAdd (a • x)) : ↥(commV ρ.range)) : V) ∈ wOff ρ W₀ := by
    intro x hx a
    have hx0 : x ≠ 0 := fun h => hx (by rw [h]; rfl)
    obtain ⟨g, hg⟩ := exists_mulVec_e0_eq hx0
    rw [← hg, ← Matrix.mulVec_smul, symm_mulVec β hβ]
    refine pt_le_wOff hx ?_
    rw [pt_eq hW₀ hg]
    exact rho_mem_map_rho g (point_mem_of_invariant β hβ inf_le_right hDne hDK a).1
  intro c hc
  set y := Multiplicative.toAdd (β ⟨c, hc⟩) with hy
  have hcy : c = ((β.symm (Multiplicative.ofAdd y) : ↥(commV ρ.range)) : V) := by
    rw [hy, ofAdd_toAdd, MulEquiv.symm_apply_apply]
  have hdec : y = (y 2 - y 0 - y 1) • ![0, 0, 1] + y 0 • ![1, 0, 1] + y 1 • ![0, 1, 1] := by
    funext k
    fin_cases k <;> simp
    ring
  rw [hcy, hdec, ofAdd_add, ofAdd_add, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hPx _ (by simp) _) (hPx _ (by simp) _))
    (hPx _ (by simp) _)

theorem commV_eq_top [Finite V] {W₀ : Subgroup V} (hW : wOff ρ W₀ = ⊤)
    (hR : Nat.card ↥(G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) (wOff ρ W₀)) ≤
      Nat.card F) :
    commV ρ.range = ⊤ := by
  set R := G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) (wOff ρ W₀) with hRdef
  set t := rootElt 0 2 (1 : F) with htdef
  have htR : ∀ v : V, ρ t v * v⁻¹ ∈ R := fun v =>
    G6.mem_commOn_of_mem (Subgroup.mem_map.mpr ⟨t, rootElt_mem_rootGroup 0 2 1, rfl⟩)
      (hW ▸ Subgroup.mem_top v)
  let c : F → V := fun a => ((β.symm (Multiplicative.ofAdd (a • ![0, 0, 1])) :
    ↥(commV ρ.range)) : V)
  have hc : ∀ a : F, ρ t (c a) * (c a)⁻¹ =
      ((β.symm (Multiplicative.ofAdd (a • ![1, 0, 0])) : ↥(commV ρ.range)) : V) := by
    intro a
    have h1 : ρ t (c a) = ((β.symm (Multiplicative.ofAdd (a • ![0, 0, 1] + a • ![1, 0, 0])) :
        ↥(commV ρ.range)) : V) := by
      rw [← symm_mulVec β hβ, htdef, rootElt02_mulVec]
      congr 3
      funext k
      fin_cases k <;> simp
    rw [h1, ofAdd_add, map_mul, Subgroup.coe_mul, mul_comm, ← mul_assoc, inv_mul_cancel,
      one_mul]
  let φ : F → ↥R := fun a => ⟨ρ t (c a) * (c a)⁻¹, htR (c a)⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have h := congrArg Subtype.val hab
    change ρ t (c a) * (c a)⁻¹ = ρ t (c b) * (c b)⁻¹ at h
    rw [hc, hc] at h
    have h2 := congrArg (fun x : V => x) h
    have h3 := Subtype.ext h2
    have h4 := congrArg Multiplicative.toAdd (β.symm.injective h3)
    simp only [toAdd_ofAdd] at h4
    have := congrFun h4 0
    simpa using this
  have hbij := hφ.bijective_of_nat_card_le hR
  rw [eq_top_iff]
  intro v _
  obtain ⟨a, ha⟩ := hbij.2 ⟨ρ t v * v⁻¹, htR v⟩
  have ha' : ρ t (c a) * (c a)⁻¹ = ρ t v * v⁻¹ := congrArg Subtype.val ha
  have hfix : ρ t (v * (c a)⁻¹) = v * (c a)⁻¹ := by
    rw [map_mul, map_inv]
    calc ρ t v * (ρ t (c a))⁻¹ = (ρ t v * v⁻¹) * v * (ρ t (c a))⁻¹ := by group
      _ = (ρ t (c a) * (c a)⁻¹) * v * (ρ t (c a))⁻¹ := by rw [ha']
      _ = v * (c a)⁻¹ := by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
  have hmem := mem_commV_of_fix β hβ hfixV (rootElt_mul_self 0 2 1) rootElt021_ne_one hfix
  have hca : c a ∈ commV ρ.range := (β.symm (Multiplicative.ofAdd (a • ![0, 0, 1]))).2
  have := Subgroup.mul_mem _ hmem hca
  rwa [inv_mul_cancel_right] at this

end Close

end CFSG.Quasithin.MS93.M16
