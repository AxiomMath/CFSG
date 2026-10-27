module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P0Tr
public import CFSG.Quasithin.EmptyFaithful.S14612EC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P0Rk

public section

namespace CFSG.Quasithin

section Generic

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U W : Subgroup V}

omit [Finite V] in
theorem autSub_zpowers {x : MulAut V} (hx : x ∈ stabSub U) :
    autSub (Subgroup.zpowers x) U = Subgroup.zpowers (resHom U ⟨x, hx⟩) := by
  ext φ
  rw [mem_autSub, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨n, ?_⟩
    have hgn : g = (⟨x, hx⟩ : stabSub U) ^ n :=
      Subtype.ext (by rw [Subgroup.coe_zpow]; exact hn.symm)
    rw [hgn, map_zpow]
  · rintro ⟨n, rfl⟩
    refine ⟨(⟨x, hx⟩ : stabSub U) ^ n, ?_, ?_⟩
    · rw [Subgroup.coe_zpow]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) n
    · rw [map_zpow]

omit [Finite V] in
theorem rk_commV_eq_of_suppData (hS : SuppData G U W) {A : Subgroup (MulAut V)} (hA : A ≤ G) :
    rk (commV A) = rk (commV (autSub A U)) := by
  have h1 : commV A = (commV (autSub A U)).map U.subtype := by
    rw [commV_eq_commSub, hS.commSub_top hA, commSub_eq_map_commV (hA.trans hS.stab)]
  unfold rk
  conv_lhs => rw [h1, Subgroup.card_map_of_injective U.subtype_injective]

end Generic

section Rho

variable {Hh : Type} [Group Hh] {W : Type} [CommGroup W] [Finite W] {ρ : Hh →* MulAut W}
  {Tb P : Subgroup (MulAut ↥(kOf ρ))}

omit [Finite W] in
theorem orderOf_resBeta_eq (hsplit : ∀ w : W, ∃ a ∈ kOf ρ, ∃ c ∈ fixV ρ.range, w = a * c)
    (x : Hh) : orderOf (resBeta ρ x) = orderOf (ρ x) := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [← map_pow, ← map_pow, ← MonoidHom.mem_ker, ← MonoidHom.mem_ker, ker_resBeta ρ hsplit]

omit [Finite W] in
theorem resBeta_eq_of_rhoH_eq (hsplit : ∀ w : W, ∃ a ∈ kOf ρ, ∃ c ∈ fixV ρ.range, w = a * c)
    {x y : Hh} (h : ρ x = ρ y) : resBeta ρ x = resBeta ρ y := by
  have : x⁻¹ * y ∈ (resBeta ρ).ker := by
    rw [ker_resBeta ρ hsplit, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rwa [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at this

omit [Finite W] in
theorem resBeta_ne_one_iff (hsplit : ∀ w : W, ∃ a ∈ kOf ρ, ∃ c ∈ fixV ρ.range, w = a * c)
    (x : Hh) : resBeta ρ x ≠ 1 ↔ ρ x ≠ 1 := by
  rw [Ne, Ne, ← MonoidHom.mem_ker, ← MonoidHom.mem_ker, ker_resBeta ρ hsplit]

theorem exists_of_map_mem_Qset (hsplit : ∀ w : W, ∃ a ∈ kOf ρ, ∃ c ∈ fixV ρ.range, w = a * c)
    (hinf : kOf ρ ⊓ fixV ρ.range = ⊥) (h : E9Z4Str (resBeta ρ).range Tb P) {B : Subgroup Hh}
    (hB : B.map ρ ∈ Qset ρ.range) :
    ∃ x ∈ B, orderOf (ρ x) = 2 ∧ B.map ρ = Subgroup.zpowers (ρ x) ∧
      ∀ b ∈ B, ρ b = 1 ∨ ρ b = ρ x := by
  have h' : E9Z4Str (autSub ρ.range (kOf ρ)) Tb P := by rwa [← range_resBeta ρ]
  have hS := suppData_split ρ hsplit hinf
  rw [E9Z4Str.Qset_eq_of_suppData hS h'] at hB
  obtain ⟨y, hy, hy2, hBy⟩ := hB
  have hyB : y ∈ B.map ρ := by rw [hBy]; exact Subgroup.mem_zpowers y
  obtain ⟨x, hxB, rfl⟩ := Subgroup.mem_map.mp hyB
  refine ⟨x, hxB, hy2, hBy, fun b hb => ?_⟩
  have : ρ b ∈ Subgroup.zpowers (ρ x) := hBy ▸ Subgroup.mem_map_of_mem ρ hb
  exact E9Z4Str.eq_one_or_eq_of_mem_zpowers hy2 this

theorem two_le_rk_commV_rho (hsplit : ∀ w : W, ∃ a ∈ kOf ρ, ∃ c ∈ fixV ρ.range, w = a * c)
    (hinf : kOf ρ ⊓ fixV ρ.range = ⊥) (h : E9Z4Str (resBeta ρ).range Tb P) {x : Hh}
    (hx : ρ x ≠ 1) : 2 ≤ rk (commV (Subgroup.zpowers (ρ x))) := by
  have hS := suppData_split ρ hsplit hinf
  have hA : Subgroup.zpowers (ρ x) ≤ ρ.range := Subgroup.zpowers_le.mpr ⟨x, rfl⟩
  rw [rk_commV_eq_of_suppData hS hA, autSub_zpowers (rho_mem_stabSub ρ x)]
  exact h.two_le_rk_commV (X := (resBeta ρ).range) ⟨x, rfl⟩ ((resBeta_ne_one_iff hsplit x).mpr hx)

end Rho

end CFSG.Quasithin
