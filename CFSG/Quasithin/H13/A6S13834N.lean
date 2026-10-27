module

public import CFSG.Quasithin.H13.A6S13834T

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7


@[expose] def tvG2 : Perm (Fin 6) := swap 1 4 * swap 4 5 * swap 5 3 * swap 3 2

@[expose] def tvR5 : Perm (Fin 6) := swap 1 4 * swap 4 3 * swap 3 5 * swap 5 2

@[expose] def tvS : Perm (Fin 6) := swap 1 3 * swap 3 4 * swap 4 5 * swap 5 2

theorem cert_tv :
    (swap 3 4 * swap 4 5 : Perm (Fin 6)) * swap 0 1 = swap 0 1 * (swap 3 4 * swap 4 5) ∧
    (swap 2 4 * swap 4 3 : Perm (Fin 6)) * swap 0 1 = swap 0 1 * (swap 2 4 * swap 4 3) ∧
    ((swap 3 4 * swap 4 5) * (swap 1 2 * swap 4 5))⁻¹ * (swap 1 2 * swap 3 4) ∈ cList ∧
    ((swap 2 4 * swap 4 3) * (swap 1 2 * swap 3 5))⁻¹ * tvR5 ∈ cList ∧
    ((swap 1 2 * swap 4 5) * swap 0 1 * (swap 1 2 * swap 4 5))⁻¹ * (tvG2 * swap 0 1 * tvR5) ∈
      cList ∧
    ((swap 1 2 * swap 4 5) * swap 0 1 * (swap 1 2 * swap 3 4))⁻¹ * (tvG2 * tvR5) ∈ cList ∧
    ((swap 1 2 * swap 4 5) * (swap 1 2 * swap 3 4))⁻¹ * (tvG2 * (swap 1 2 * swap 3 5)) ∈ cList ∧
    (1 : Perm (Fin 6))⁻¹ * ((swap 1 2 * swap 4 5) * (swap 1 2 * swap 4 5)) ∈ cList ∧
    (tvG2 * swap 0 1 * (swap 1 2 * swap 3 5))⁻¹ * tvS ∈ cList := by
  decide +kernel

theorem cert_tv_signs : Perm.sign (swap 1 2 * swap 4 5 : Perm (Fin 6)) = 1 ∧
    Perm.sign tvG2 = 1 ∧ Perm.sign (swap 1 2 * swap 3 4 : Perm (Fin 6)) = 1 ∧
    Perm.sign (swap 1 2 * swap 3 5 : Perm (Fin 6)) = 1 ∧ Perm.sign tvR5 = 1 ∧
    Perm.sign (swap 3 4 * swap 4 5 : Perm (Fin 6)) = 1 ∧
    Perm.sign (swap 2 4 * swap 4 3 : Perm (Fin 6)) = 1 ∧ Perm.sign tvS = 1 ∧
    tvS * iota0 ≠ iota0 * tvS := by
  decide +kernel


namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section NoTransv

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  (hN : ∀ g : ↥S.G1, ρ g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  (h13315 : Stmt13_3_15) {v₀ : G} (hv₀ : v₀ ∈ V) (hv₀3 : v₀ ∉ S.V3)
include hN h13315 hv₀ hv₀3

theorem exists_pointGroup (hVH : IsElemAbelian 2 (conjClosure V S.G1)) (hVab : IsElemAbelian 2 V) :
    ∃ (W : Type) (_ : Group W) (f : ↥S.G1 → W),
      (∀ k k' : ↥S.G1, ρ k⁻¹ * ρ k' ∈ cList → f k = f k') ∧ (∀ k, f k * f k = 1) ∧
      (∀ k k', f k * f k' = f k' * f k) ∧
      (∀ a b c d : ↥S.G1, ((a : G) * v₀ * (a : G)⁻¹) * ((b : G) * v₀ * (b : G)⁻¹)⁻¹ *
        (((c : G) * v₀ * (c : G)⁻¹) * ((d : G) * v₀ * (d : G)⁻¹)⁻¹)⁻¹ ∈
          conjClosure S.V3 S.G1 → f a * (f b)⁻¹ = f c * (f d)⁻¹) ∧
      ∀ y : ↥S.G1, f y = f 1 → (y : G) * v₀ * (y : G)⁻¹ * v₀⁻¹ ∈ conjClosure S.V3 S.G1 := by
  have : IsMulCommutative ↥(conjClosure V S.G1) := hVH.1
  have hp : ∀ k : ↥S.G1, (k : G) * v₀ * (k : G)⁻¹ ∈ conjClosure V S.G1 := fun k =>
    mem_conjClosure k.2 hv₀
  let U' : Subgroup ↥(conjClosure V S.G1) :=
    (conjClosure S.V3 S.G1).subgroupOf (conjClosure V S.G1)
  let f : ↥S.G1 → ↥(conjClosure V S.G1) ⧸ U' := fun k =>
    QuotientGroup.mk (⟨_, hp k⟩ : ↥(conjClosure V S.G1))
  have hv2 : v₀ ^ 2 = 1 := isElemAbelian_pow_eq_one hVab hv₀
  refine ⟨_, inferInstance, f, fun k k' h => ?_, fun k => ?_, fun k k' => ?_, fun a b c d h => ?_,
    fun y hy => ?_⟩
  · refine QuotientGroup.eq.2 ?_
    rw [Subgroup.mem_subgroupOf]
    exact S.point_congr hN h13315 hv₀ hv₀3 h
  · rw [← QuotientGroup.mk_mul]
    have e : (⟨_, hp k⟩ : ↥(conjClosure V S.G1)) * ⟨_, hp k⟩ = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, OneMemClass.coe_one]
      calc (k : G) * v₀ * (k : G)⁻¹ * ((k : G) * v₀ * (k : G)⁻¹) =
          (k : G) * (v₀ * v₀) * (k : G)⁻¹ := by group
        _ = 1 := by rw [← pow_two, hv2]; group
    rw [e, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      mul_comm' (⟨_, hp k⟩ : ↥(conjClosure V S.G1))]
  · have hmem : (⟨_, hp a⟩ * (⟨_, hp b⟩ : ↥(conjClosure V S.G1))⁻¹ *
        (⟨_, hp c⟩ * (⟨_, hp d⟩ : ↥(conjClosure V S.G1))⁻¹)⁻¹ : ↥(conjClosure V S.G1)) ∈ U' := by
      rw [Subgroup.mem_subgroupOf]
      exact h
    have h2 := (QuotientGroup.eq_one_iff _).2 hmem
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv, mul_inv_eq_one] at h2
    exact h2
  · have hmem := QuotientGroup.eq.1 hy
    rw [Subgroup.mem_subgroupOf] at hmem
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, OneMemClass.coe_one] at hmem
    rw [one_mul, inv_one, mul_one] at hmem
    have hyv : (y : G) * v₀ * (y : G)⁻¹ * v₀ = v₀ * ((y : G) * v₀ * (y : G)⁻¹) :=
      isElemAbelian_comm hVH (hp y) (le_conjClosure V S.G1 hv₀)
    have e : (y : G) * v₀ * (y : G)⁻¹ * v₀⁻¹ = (((y : G) * v₀ * (y : G)⁻¹)⁻¹ * v₀)⁻¹ := by
      calc (y : G) * v₀ * (y : G)⁻¹ * v₀⁻¹ =
          v₀⁻¹ * (v₀ * ((y : G) * v₀ * (y : G)⁻¹)) * v₀⁻¹ := by group
        _ = v₀⁻¹ * ((y : G) * v₀ * (y : G)⁻¹ * v₀) * v₀⁻¹ := by rw [hyv]
        _ = (((y : G) * v₀ * (y : G)⁻¹)⁻¹ * v₀)⁻¹ := by group
    rw [e]
    exact (conjClosure S.V3 S.G1).inv_mem hmem

theorem fix_all_gen {K : Subgroup G} (hKT : K ⊔ T = S.G1)
    (honto : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ k = σ)
    (hKA : ∀ k : ↥S.G1, (k : G) ∈ K → ρ k ∈ alternatingGroup (Fin 6))
    (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1) (hQT : pCoreOf 2 S.G1 ≤ T)
    {s : Perm (Fin 6)} (hs1 : Perm.sign s = 1) (hsC : s * iota0 ≠ iota0 * s)
    {x : ↥S.G1} (hx : ρ x = s)
    (hxv : (x : G) * v₀ * (x : G)⁻¹ * v₀⁻¹ ∈ conjClosure S.V3 S.G1) :
    ∀ h ∈ S.G1, h * v₀ * h⁻¹ * v₀⁻¹ ∈ conjClosure S.V3 S.G1 := by
  set U := conjClosure S.V3 S.G1 with hU
  have hUN : ∀ k ∈ S.G1, ∀ u ∈ U, k * u * k⁻¹ ∈ U := fun k hk u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hk) u).mp hu
  let Fix : Subgroup G :=
    { carrier := {h | h ∈ S.G1 ∧ h * v₀ * h⁻¹ * v₀⁻¹ ∈ U}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨S.G1.mul_mem ha hb, ?_⟩
        have e : a * b * v₀ * (a * b)⁻¹ * v₀⁻¹ =
            (a * (b * v₀ * b⁻¹ * v₀⁻¹) * a⁻¹) * (a * v₀ * a⁻¹ * v₀⁻¹) := by group
        rw [e]
        exact U.mul_mem (hUN a ha _ hb') ha'
      one_mem' := ⟨S.G1.one_mem, by rw [one_mul, inv_one, mul_one, mul_inv_cancel]; exact U.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨S.G1.inv_mem ha, ?_⟩
        have e : a⁻¹ * v₀ * a⁻¹⁻¹ * v₀⁻¹ = a⁻¹ * (a * v₀ * a⁻¹ * v₀⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact hUN _ (S.G1.inv_mem ha) _ (U.inv_mem ha') }
  have hmemFix : ∀ h, h ∈ Fix ↔ h ∈ S.G1 ∧ h * v₀ * h⁻¹ * v₀⁻¹ ∈ U := fun h => Iff.rfl
  have hNfix : ∀ g : ↥S.G1, (g : G) ∈ Subgroup.normalizer (S.V3 : Set G) → (g : G) ∈ Fix :=
    fun g hg => (hmemFix _).2 ⟨g.2, S.comm_mem_of_normalizer h13315 hv₀ hv₀3 g.2 hg⟩
  set X := (Fix.subgroupOf S.G1).map ρ with hX
  have hCX : cA6 ≤ X := by
    intro σ hσ
    obtain ⟨k, -, hk⟩ := honto σ (Equiv.Perm.mem_alternatingGroup.mpr hσ.2)
    refine ⟨k, Subgroup.mem_subgroupOf.mpr (hNfix k ((hN k).1 ?_)), hk⟩
    rw [hk]
    exact mem_cList σ hσ.1
  have hsX : s ∈ X := ⟨x, Subgroup.mem_subgroupOf.mpr ((hmemFix _).2 ⟨x.2, hxv⟩), hx⟩
  have hA6 := alt6_le_of_overgroup hCX hsX hs1 hsC
  have hTH : T ≤ S.G1 := hKT ▸ le_sup_right
  have hTFix : T ≤ Fix := fun t ht =>
    hNfix ⟨t, hTH ht⟩ (S.T_le_normalizer_V3 ht)
  have hKFix : K ≤ Fix := by
    intro k hk
    have hkH : k ∈ S.G1 := hKT ▸ Subgroup.mem_sup_left hk
    obtain ⟨f, hf, hfk⟩ := hA6 (hKA ⟨k, hkH⟩ hk)
    have hfF : (f : G) ∈ Fix := Subgroup.mem_subgroupOf.mp hf
    have h1 : ρ (f⁻¹ * ⟨k, hkH⟩) = 1 := by rw [map_mul, map_inv, hfk, inv_mul_cancel]
    have hQ := (hker _).1 h1
    have hF2 : ((f⁻¹ * ⟨k, hkH⟩ : ↥S.G1) : G) ∈ Fix := hTFix (hQT hQ)
    have e : k = (f : G) * ((f⁻¹ * ⟨k, hkH⟩ : ↥S.G1) : G) := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group
    rw [e]
    exact Fix.mul_mem hfF hF2
  have hall : S.G1 ≤ Fix := hKT ▸ sup_le hKFix hTFix
  exact fun h hh => ((hmemFix h).1 (hall hh)).2

end NoTransv

end Setting4


namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section NoTransv2

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  (hN : ∀ g : ↥S.G1, ρ g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  (h13315 : Stmt13_3_15) {v₀ : G} (hv₀ : v₀ ∈ V) (hv₀3 : v₀ ∉ S.V3)
include hN h13315 hv₀ hv₀3

theorem transv_rel (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
    (hQU : ∀ q ∈ pCoreOf 2 S.G1, ∀ y ∈ conjClosure V S.G1,
      q * y * q⁻¹ * y⁻¹ ∈ conjClosure S.V3 S.G1) (hVle : V ≤ S.G1)
    {x : ↥S.G1} (hx : ρ x = swap 0 1)
    (htv : ∀ y ∈ conjClosure V S.G1, ∀ y' ∈ conjClosure V S.G1,
      (x : G) * y * (x : G)⁻¹ * y⁻¹ ∉ conjClosure S.V3 S.G1 →
      (x : G) * y' * (x : G)⁻¹ * y'⁻¹ ∉ conjClosure S.V3 S.G1 →
      ((x : G) * y * (x : G)⁻¹ * y⁻¹)⁻¹ * ((x : G) * y' * (x : G)⁻¹ * y'⁻¹) ∈
        conjClosure S.V3 S.G1)
    {c k k' : ↥S.G1} (hc : ρ c * swap 0 1 = swap 0 1 * ρ c)
    (hkk : (ρ c * ρ k)⁻¹ * ρ k' ∈ cList) :
    ((x : G) * ((k : G) * v₀ * (k : G)⁻¹) * (x : G)⁻¹ * ((k : G) * v₀ * (k : G)⁻¹)⁻¹) *
      ((x : G) * ((k' : G) * v₀ * (k' : G)⁻¹) * (x : G)⁻¹ *
        ((k' : G) * v₀ * (k' : G)⁻¹)⁻¹)⁻¹ ∈ conjClosure S.V3 S.G1 := by
  set U := conjClosure S.V3 S.G1 with hU
  have hUN : ∀ g ∈ S.G1, ∀ u ∈ U, g * u * g⁻¹ ∈ U := fun g hg u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hg) u).mp hu
  have hVHH : conjClosure V S.G1 ≤ S.G1 := conjClosure_le fun g hg v hv =>
    S.G1.mul_mem (S.G1.mul_mem hg (hVle hv)) (S.G1.inv_mem hg)
  have hp : ∀ m : ↥S.G1, (m : G) * v₀ * (m : G)⁻¹ ∈ conjClosure V S.G1 := fun m =>
    mem_conjClosure m.2 hv₀
  set X : G := (x : G) with hX
  set P : ↥S.G1 → G := fun m => (m : G) * v₀ * (m : G)⁻¹ with hP
  set d : ↥S.G1 → G := fun m => X * P m * X⁻¹ * (P m)⁻¹ with hd
  change d k * (d k')⁻¹ ∈ U
  set q : G := X⁻¹ * ((c : G) * X * (c : G)⁻¹) with hq
  have hqQ : q ∈ pCoreOf 2 S.G1 := by
    have h1 : ρ (x⁻¹ * (c * x * c⁻¹)) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hx]
      calc (swap 0 1)⁻¹ * (ρ c * swap 0 1 * (ρ c)⁻¹) =
          (swap (0 : Fin 6) 1)⁻¹ * (swap 0 1 * ρ c * (ρ c)⁻¹) := by rw [hc]
        _ = 1 := by group
    have := (hker _).1 h1
    simpa [hq, hX] using this
  have hA : (c : G) * d k * (c : G)⁻¹ =
      (X * q) * P (c * k) * (X * q)⁻¹ * (P (c * k))⁻¹ := by
    simp only [hd, hP, hq, Subgroup.coe_mul]
    group
  have h1 : ∀ z ∈ conjClosure V S.G1,
      ((X * q) * z * (X * q)⁻¹ * z⁻¹) * (X * z * X⁻¹ * z⁻¹)⁻¹ ∈ U := by
    intro z hz
    have e : ((X * q) * z * (X * q)⁻¹ * z⁻¹) * (X * z * X⁻¹ * z⁻¹)⁻¹ =
        X * (q * z * q⁻¹ * z⁻¹) * X⁻¹ := by group
    rw [e]
    exact hUN X x.2 _ (hQU q hqQ z hz)
  have h2 : (P (c * k))⁻¹ * P k' ∈ U :=
    S.point_congr hN h13315 hv₀ hv₀3 (k := c * k) (k' := k') (by rw [map_inv, map_mul]; exact hkk)
  have h3 : (X * P (c * k) * X⁻¹ * (P (c * k))⁻¹) * (d k')⁻¹ ∈ U := by
    set u := (P (c * k))⁻¹ * P k' with hu
    have hz : P k' = P (c * k) * u := by rw [hu]; group
    have e : (X * P (c * k) * X⁻¹ * (P (c * k))⁻¹) * (d k')⁻¹ =
        (X * P (c * k)) * (X⁻¹ * u * X * u⁻¹) * (X * P (c * k))⁻¹ := by
      simp only [hd]
      rw [hz]
      group
    rw [e]
    have hxz : X * P (c * k) ∈ S.G1 := S.G1.mul_mem x.2 (hVHH (hp (c * k)))
    refine hUN _ hxz _ (U.mul_mem ?_ (U.inv_mem h2))
    have := hUN X⁻¹ (S.G1.inv_mem x.2) u h2
    rwa [inv_inv] at this
  have hA' : (c : G) * d k * (c : G)⁻¹ * (d k')⁻¹ ∈ U := by
    rw [hA]
    have e : (X * q) * P (c * k) * (X * q)⁻¹ * (P (c * k))⁻¹ * (d k')⁻¹ =
        (((X * q) * P (c * k) * (X * q)⁻¹ * (P (c * k))⁻¹) *
          (X * P (c * k) * X⁻¹ * (P (c * k))⁻¹)⁻¹) *
        ((X * P (c * k) * X⁻¹ * (P (c * k))⁻¹) * (d k')⁻¹) := by group
    rw [e]
    exact U.mul_mem (h1 _ (hp (c * k))) h3
  have hcd : ∀ y : G, y ∈ U ↔ (c : G) * y * (c : G)⁻¹ ∈ U := fun y => by
    refine ⟨fun h => hUN _ c.2 _ h, fun h => ?_⟩
    have := hUN _ (S.G1.inv_mem c.2) _ h
    rwa [show (c : G)⁻¹ * ((c : G) * y * (c : G)⁻¹) * (c : G)⁻¹⁻¹ = y by group] at this
  by_cases hk : d k ∈ U
  · have h4 : (c : G) * d k * (c : G)⁻¹ ∈ U := (hcd _).1 hk
    have h5 : (d k')⁻¹ ∈ U := by
      have := U.mul_mem (U.inv_mem h4) hA'
      rwa [show ((c : G) * d k * (c : G)⁻¹)⁻¹ * ((c : G) * d k * (c : G)⁻¹ * (d k')⁻¹) =
        (d k')⁻¹ by group] at this
    exact U.mul_mem hk h5
  · have h4 : (c : G) * d k * (c : G)⁻¹ ∉ U := fun h => hk ((hcd _).2 h)
    have h5 : d k' ∉ U := fun h => h4 (by
      have := U.mul_mem hA' h
      rwa [show (c : G) * d k * (c : G)⁻¹ * (d k')⁻¹ * d k' = (c : G) * d k * (c : G)⁻¹ by
        group] at this)
    have h6 := htv _ (hp k) _ (hp k') hk h5
    have hdkH : d k ∈ S.G1 := by
      simp only [hd]
      exact S.G1.mul_mem (S.G1.mul_mem (S.G1.mul_mem x.2 (hVHH (hp k))) (S.G1.inv_mem x.2))
        (S.G1.inv_mem (hVHH (hp k)))
    have := hUN _ hdkH _ (U.inv_mem h6)
    rwa [show d k * ((d k)⁻¹ * d k')⁻¹ * (d k)⁻¹ = d k * (d k')⁻¹ by group] at this

end NoTransv2

end Setting4


namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section NoTransv3

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  (hN : ∀ g : ↥S.G1, ρ g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  (h13315 : Stmt13_3_15) {v₀ : G} (hv₀ : v₀ ∈ V) (hv₀3 : v₀ ∉ S.V3)
include hN h13315 hv₀ hv₀3

theorem fixed_of_transv01 (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
    (hQU : ∀ q ∈ pCoreOf 2 S.G1, ∀ y ∈ conjClosure V S.G1,
      q * y * q⁻¹ * y⁻¹ ∈ conjClosure S.V3 S.G1) (hVle : V ≤ S.G1)
    (hVH : IsElemAbelian 2 (conjClosure V S.G1)) (hVab : IsElemAbelian 2 V)
    (honto : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, ρ k = σ)
    {x : ↥S.G1} (hx : ρ x = swap 0 1)
    (htv : ∀ y ∈ conjClosure V S.G1, ∀ y' ∈ conjClosure V S.G1,
      (x : G) * y * (x : G)⁻¹ * y⁻¹ ∉ conjClosure S.V3 S.G1 →
      (x : G) * y' * (x : G)⁻¹ * y'⁻¹ ∉ conjClosure S.V3 S.G1 →
      ((x : G) * y * (x : G)⁻¹ * y⁻¹)⁻¹ * ((x : G) * y' * (x : G)⁻¹ * y'⁻¹) ∈
        conjClosure S.V3 S.G1) :
    ∃ y : ↥S.G1, ρ y = tvS ∧ (y : G) * v₀ * (y : G)⁻¹ * v₀⁻¹ ∈ conjClosure S.V3 S.G1 := by
  set U := conjClosure S.V3 S.G1 with hU
  have hUN : ∀ g ∈ S.G1, ∀ u ∈ U, g * u * g⁻¹ ∈ U := fun g hg u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hg) u).mp hu
  obtain ⟨W, _, f, fcong, fsq, fcomm, toW, fromW⟩ :=
    S.exists_pointGroup hN h13315 hv₀ hv₀3 hVH hVab
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, -⟩ := cert_tv_signs
  have lift : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 → ∃ k : ↥S.G1, ρ k = σ := fun σ hσ =>
    honto σ (Perm.mem_alternatingGroup.mpr hσ)
  obtain ⟨G₁, hG₁⟩ := lift _ s1
  obtain ⟨G₂, hG₂⟩ := lift _ s2
  obtain ⟨R₁, hR₁⟩ := lift _ s3
  obtain ⟨R₂, hR₂⟩ := lift _ s4
  obtain ⟨R₅, hR₅⟩ := lift _ s5
  obtain ⟨C₁, hC₁⟩ := lift _ s6
  obtain ⟨C₂, hC₂⟩ := lift _ s7
  obtain ⟨Y, hY⟩ := lift _ s8
  obtain ⟨c1, c2, k1, k2, i1, i2, i3, i4, i5⟩ := cert_tv
  have rel1 := S.transv_rel hN h13315 hv₀ hv₀3 hker hQU hVle hx htv (c := C₁) (k := G₁) (k' := R₁)
    (by rw [hC₁]; exact c1) (by rw [hC₁, hG₁, hR₁]; exact k1)
  have rel2 := S.transv_rel hN h13315 hv₀ hv₀3 hker hQU hVle hx htv (c := C₂) (k := R₂) (k' := R₅)
    (by rw [hC₂]; exact c2) (by rw [hC₂, hR₂, hR₅]; exact k2)
  have conj : ∀ (g k k' : ↥S.G1),
      ((x : G) * ((k : G) * v₀ * (k : G)⁻¹) * (x : G)⁻¹ * ((k : G) * v₀ * (k : G)⁻¹)⁻¹) *
        ((x : G) * ((k' : G) * v₀ * (k' : G)⁻¹) * (x : G)⁻¹ *
          ((k' : G) * v₀ * (k' : G)⁻¹)⁻¹)⁻¹ ∈ U →
      f (g * x * k) * (f (g * k))⁻¹ = f (g * x * k') * (f (g * k'))⁻¹ := by
    intro g k k' h
    refine toW _ _ _ _ ?_
    have := hUN _ g.2 _ h
    simp only [Subgroup.coe_mul]
    convert this using 1
    group
  have e1 := conj G₁ G₁ R₁ rel1
  have e2 := conj G₂ R₂ R₅ rel2
  have f1 : f (G₁ * x * G₁) = f (G₂ * x * R₅) := fcong _ _ (by
    simp only [map_mul, map_inv, hG₁, hG₂, hx, hR₅]; exact i1)
  have f2 : f (G₁ * x * R₁) = f (G₂ * R₅) := fcong _ _ (by
    simp only [map_mul, map_inv, hG₁, hG₂, hx, hR₁, hR₅]; exact i2)
  have f3 : f (G₁ * R₁) = f (G₂ * R₂) := fcong _ _ (by
    simp only [map_mul, map_inv, hG₁, hG₂, hR₁, hR₂]; exact i3)
  have f4 : f 1 = f (G₁ * G₁) := fcong _ _ (by
    simp only [map_mul, map_inv, map_one, hG₁]; exact i4)
  have f5 : f (G₂ * x * R₂) = f Y := fcong _ _ (by
    simp only [map_mul, map_inv, hG₂, hx, hR₂, hY]; exact i5)
  refine ⟨Y, hY, fromW Y ?_⟩
  rw [← f5, f4]
  rw [← f1, ← f2, ← f3] at e2
  have hac := fcomm (G₁ * x * G₁) (G₁ * x * R₁)
  have hci := inv_eq_of_mul_eq_one_right (fsq (G₁ * x * R₁))
  have hd := fcomm (G₁ * x * G₁) (G₁ * R₁)
  have hdc := fcomm (G₁ * x * R₁) (G₁ * R₁)
  generalize f (G₁ * x * G₁) = a at e1 e2 hac hd
  generalize f (G₁ * G₁) = b at e1 ⊢
  generalize f (G₁ * x * R₁) = c at e1 e2 hac hci hdc
  generalize f (G₁ * R₁) = d at e1 e2 hd hdc
  generalize f (G₂ * x * R₂) = e at e2 ⊢
  have hb : b = d * c⁻¹ * a := by
    have : b⁻¹ = a⁻¹ * (c * d⁻¹) := by rw [← e1]; group
    calc b = (b⁻¹)⁻¹ := by rw [inv_inv]
      _ = d * c⁻¹ * a := by rw [this]; group
  have he : e = a * c⁻¹ * d := by
    calc e = (e * d⁻¹) * d := by group
      _ = a * c⁻¹ * d := by rw [e2]
  rw [he, hb, hci]
  calc a * c * d = a * (d * c) := by rw [mul_assoc, hdc]
    _ = d * a * c := by rw [← mul_assoc, hd]
    _ = d * c * a := by rw [mul_assoc, hac, ← mul_assoc]

end NoTransv3

end Setting4


open scoped commutatorElement

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_V_not_V3 : ∃ v₀ ∈ V, v₀ ∉ S.V3 := by
  by_contra h
  push Not at h
  have h1 := Subgroup.relIndex_eq_one.mpr (show V ≤ S.V3 from h)
  rw [S.relIndex_V3_V] at h1
  exact absurd h1 (by norm_num)

section Transv

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  (hN : ∀ g : ↥S.G1, ρ g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  (h13315 : Stmt13_3_15)
include hN h13315

theorem false_of_transv (hNS : ¬ LieModel G .PSp 3 2 1)
    (h1356two : Input1356Two) (hG1 : S.G1 ∈ S.Hz) (h13314 : Stmt13_3_14)
    {K : Subgroup G} (hKT : K ⊔ T = S.G1)
    (honto : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ k = σ)
    (hKA : ∀ k : ↥S.G1, (k : G) ∈ K → ρ k ∈ alternatingGroup (Fin 6))
    (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1) (hQT : pCoreOf 2 S.G1 ≤ T)
    (hVle : V ≤ S.G1) (hVH : IsElemAbelian 2 (conjClosure V S.G1)) (hVab : IsElemAbelian 2 V)
    {x : ↥S.G1} (hx : ρ x = swap 0 1 ∨ ρ x = swap 2 3 ∨ ρ x = swap 4 5)
    (htv : ∀ y ∈ conjClosure V S.G1, ∀ y' ∈ conjClosure V S.G1,
      (x : G) * y * (x : G)⁻¹ * y⁻¹ ∉ conjClosure S.V3 S.G1 →
      (x : G) * y' * (x : G)⁻¹ * y'⁻¹ ∉ conjClosure S.V3 S.G1 →
      ((x : G) * y * (x : G)⁻¹ * y⁻¹)⁻¹ * ((x : G) * y' * (x : G)⁻¹ * y'⁻¹) ∈
        conjClosure S.V3 S.G1) : False := by
  obtain ⟨v₀, hv₀, hv₀3⟩ := S.exists_V_not_V3
  set U := conjClosure S.V3 S.G1 with hU
  have hUN : ∀ g ∈ S.G1, ∀ u ∈ U, g * u * g⁻¹ ∈ U := fun g hg u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hg) u).mp hu
  have hVN : ∀ g ∈ S.G1, ∀ y ∈ conjClosure V S.G1, g * y * g⁻¹ ∈ conjClosure V S.G1 :=
    fun g hg y hy =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V S.G1 hg) y).mp hy
  have hQU : ∀ q ∈ pCoreOf 2 S.G1, ∀ y ∈ conjClosure V S.G1, q * y * q⁻¹ * y⁻¹ ∈ U := by
    intro q hq y hy
    have h := Subgroup.commutator_mem_commutator hy hq
    rw [S.comm_VH_QH_eq hNS h13315 h1356two hG1 h13314] at h
    have e : q * y * q⁻¹ * y⁻¹ = ⁅y, q⁆⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact U.inv_mem h
  obtain ⟨σ, hσ, hσx⟩ : ∃ σ : Perm (Fin 6), Perm.sign σ = 1 ∧ σ * ρ x * σ⁻¹ = swap 0 1 := by
    rcases hx with h | h | h <;> rw [h]
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨swap 0 2 * swap 1 3, by decide, by decide⟩
    · exact ⟨swap 0 4 * swap 1 5, by decide, by decide⟩
  obtain ⟨k, -, hk⟩ := honto σ (Perm.mem_alternatingGroup.mpr hσ)
  set x' : ↥S.G1 := k * x * k⁻¹ with hx'
  have hx'ρ : ρ x' = swap 0 1 := by rw [hx', map_mul, map_mul, map_inv, hk, hσx]
  have hconj : ∀ z : G, (x' : G) * z * (x' : G)⁻¹ * z⁻¹ =
      (k : G) * ((x : G) * ((k : G)⁻¹ * z * (k : G)) * (x : G)⁻¹ *
        ((k : G)⁻¹ * z * (k : G))⁻¹) * (k : G)⁻¹ := fun z => by
    simp only [hx', Subgroup.coe_mul, InvMemClass.coe_inv]
    group
  have hz : ∀ z ∈ conjClosure V S.G1, (k : G)⁻¹ * z * (k : G) ∈ conjClosure V S.G1 :=
    fun z hz => by
      have := hVN _ (S.G1.inv_mem k.2) z hz
      rwa [inv_inv] at this
  have htv' : ∀ y ∈ conjClosure V S.G1, ∀ y' ∈ conjClosure V S.G1,
      (x' : G) * y * (x' : G)⁻¹ * y⁻¹ ∉ U → (x' : G) * y' * (x' : G)⁻¹ * y'⁻¹ ∉ U →
      ((x' : G) * y * (x' : G)⁻¹ * y⁻¹)⁻¹ * ((x' : G) * y' * (x' : G)⁻¹ * y'⁻¹) ∈ U := by
    intro y hy y' hy' h1 h2
    rw [hconj y] at h1 ⊢
    rw [hconj y'] at h2 ⊢
    have h3 := htv _ (hz y hy) _ (hz y' hy') (fun h => h1 (hUN _ k.2 _ h))
      (fun h => h2 (hUN _ k.2 _ h))
    have := hUN _ k.2 _ h3
    convert this using 1
    group
  obtain ⟨y, hy, hyv⟩ := S.fixed_of_transv01 hN h13315 hv₀ hv₀3 hker hQU hVle hVH hVab
    (fun σ hσ => (honto σ hσ).elim fun k hk => ⟨k, hk.2⟩) hx'ρ htv'
  obtain ⟨-, -, -, -, -, -, -, s8, s9⟩ := cert_tv_signs
  have hall := S.fix_all_gen hN h13315 hv₀ hv₀3 hKT honto hKA hker hQT s8 s9 hy hyv
  exact S.false_of_fix h13315 hv₀ hv₀3 hNS h1356two hG1 h13314 hVle hall

end Transv

end Setting4

@[expose] def QuadCertA (f₁ f₂ g₁ m₁ g₂ m₂ s : Perm (Fin 6)) : Prop :=
  Perm.sign g₁ = 1 ∧ Perm.sign m₁ = 1 ∧ Perm.sign g₂ = 1 ∧ Perm.sign m₂ = 1 ∧
    Perm.sign s = 1 ∧ s * iota0 ≠ iota0 * s ∧
    (g₁ * m₁)⁻¹ * (g₂ * f₂ * m₂) ∈ cList ∧ (g₁ * f₁ * m₁)⁻¹ * s ∈ cList ∧
    (g₁ * f₂ * m₁)⁻¹ * (g₂ * f₂ * f₁ * m₂) ∈ cList ∧
    (g₁ * f₂ * f₁ * m₁)⁻¹ * (g₂ * f₁ * m₂) ∈ cList ∧ (1 : Perm (Fin 6))⁻¹ * (g₂ * m₂) ∈ cList

instance (f₁ f₂ g₁ m₁ g₂ m₂ s : Perm (Fin 6)) : Decidable (QuadCertA f₁ f₂ g₁ m₁ g₂ m₂ s) := by
  unfold QuadCertA
  infer_instance

theorem quadCertA_0123 : QuadCertA (swap 0 1) (swap 2 3) (swap 0 2 * swap 4 5)
    (swap 0 2 * swap 4 5 * (swap 3 4 * swap 4 5)) (swap 0 5 * swap 2 4) (swap 0 5 * swap 2 4)
    (swap 1 2 * swap 3 4) := by
  decide +kernel

theorem quadCertA_2345 : QuadCertA (swap 2 3) (swap 4 5) (swap 0 1 * swap 2 4)
    (swap 0 1 * swap 2 4 * (swap 0 1 * swap 1 5)) (swap 0 4 * swap 1 2) (swap 0 4 * swap 1 2)
    (swap 0 5 * swap 3 4) := by
  decide +kernel

theorem quadCertA_4501 : QuadCertA (swap 4 5) (swap 0 1) (swap 0 4 * swap 2 3)
    (swap 0 4 * swap 2 3 * (swap 1 2 * swap 2 3)) (swap 0 2 * swap 3 4) (swap 0 2 * swap 3 4)
    (swap 0 5 * swap 1 2) := by
  decide +kernel

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section QuadA

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  (hN : ∀ g : ↥S.G1, ρ g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  (h13315 : Stmt13_3_15) {v₀ : G} (hv₀ : v₀ ∈ V) (hv₀3 : v₀ ∉ S.V3)
include hN h13315 hv₀ hv₀3

theorem fix_of_quadA (hVH : IsElemAbelian 2 (conjClosure V S.G1)) (hVab : IsElemAbelian 2 V)
    {B : Subgroup G} (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBV : ∀ b ∈ B, ∀ y ∈ conjClosure V S.G1, b * y * b⁻¹ * y⁻¹ ∈ B)
    {b₁ b₂ : ↥S.G1} (hb₁ : (b₁ : G) ∈ B) (hb₂ : (b₂ : G) ∈ B)
    {f₁ f₂ g₁ m₁ g₂ m₂ s : Perm (Fin 6)} (hc : QuadCertA f₁ f₂ g₁ m₁ g₂ m₂ s)
    (he₁ : ρ b₁ = f₁) (he₂ : ρ b₂ = f₂) {G₁ M₁ G₂ M₂ Y : ↥S.G1} (hG₁ : ρ G₁ = g₁)
    (hM₁ : ρ M₁ = m₁) (hG₂ : ρ G₂ = g₂) (hM₂ : ρ M₂ = m₂) (hY : ρ Y = s) :
    (Y : G) * v₀ * (Y : G)⁻¹ * v₀⁻¹ ∈ conjClosure S.V3 S.G1 := by
  obtain ⟨-, -, -, -, -, -, c1, c2, c3, c4, c5⟩ := hc
  obtain ⟨W, _, f, fcong, fsq, fcomm, toW, fromW⟩ :=
    S.exists_pointGroup hN h13315 hv₀ hv₀3 hVH hVab
  have rel : ∀ g m : ↥S.G1, f (g * b₂ * b₁ * m) * (f (g * b₂ * m))⁻¹ =
      f (g * b₁ * m) * (f (g * m))⁻¹ := by
    intro g m
    refine toW _ _ _ _ ?_
    have hy : (m : G) * v₀ * (m : G)⁻¹ ∈ conjClosure V S.G1 := mem_conjClosure m.2 hv₀
    have q := quad_identity hBc hBV hb₁ hb₂ hy
    have e : ((g * b₂ * b₁ * m : ↥S.G1) : G) * v₀ * ((g * b₂ * b₁ * m : ↥S.G1) : G)⁻¹ *
        (((g * b₂ * m : ↥S.G1) : G) * v₀ * ((g * b₂ * m : ↥S.G1) : G)⁻¹)⁻¹ *
        (((g * b₁ * m : ↥S.G1) : G) * v₀ * ((g * b₁ * m : ↥S.G1) : G)⁻¹ *
          (((g * m : ↥S.G1) : G) * v₀ * ((g * m : ↥S.G1) : G)⁻¹)⁻¹)⁻¹ =
        (g : G) * (((b₂ : G) * b₁) * ((m : G) * v₀ * (m : G)⁻¹) * ((b₂ : G) * b₁)⁻¹ *
          ((b₂ : G) * ((m : G) * v₀ * (m : G)⁻¹) * (b₂ : G)⁻¹)⁻¹ *
          ((b₁ : G) * ((m : G) * v₀ * (m : G)⁻¹) * (b₁ : G)⁻¹ *
            ((m : G) * v₀ * (m : G)⁻¹)⁻¹)⁻¹) * (g : G)⁻¹ := by
      simp only [Subgroup.coe_mul]
      group
    rw [e, q, mul_inv_cancel, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  have r1 := rel G₁ M₁
  have r2 := rel G₂ M₂
  have i1 : f (G₁ * M₁) = f (G₂ * b₂ * M₂) := fcong _ _ (by
    simp only [map_mul, map_inv, hG₁, hM₁, hG₂, hM₂, he₂]; exact c1)
  have i2 : f (G₁ * b₁ * M₁) = f Y := fcong _ _ (by
    simp only [map_mul, map_inv, hG₁, hM₁, he₁, hY]; exact c2)
  have i3 : f (G₁ * b₂ * M₁) = f (G₂ * b₂ * b₁ * M₂) := fcong _ _ (by
    simp only [map_mul, map_inv, hG₁, hM₁, hG₂, hM₂, he₁, he₂]; exact c3)
  have i4 : f (G₁ * b₂ * b₁ * M₁) = f (G₂ * b₁ * M₂) := fcong _ _ (by
    simp only [map_mul, map_inv, hG₁, hM₁, hG₂, hM₂, he₁, he₂]; exact c4)
  have i5 : f 1 = f (G₂ * M₂) := fcong _ _ (by
    simp only [map_mul, map_inv, map_one, hG₂, hM₂]; exact c5)
  rw [i1, i2, i3, i4] at r1
  rw [← i5] at r2
  refine fromW Y ?_
  have hc1 := fcomm (G₂ * b₁ * M₂) (G₂ * b₂ * b₁ * M₂)
  have hc2 := fcomm (G₂ * b₁ * M₂) (G₂ * b₂ * M₂)
  have hc3 := fcomm (G₂ * b₂ * b₁ * M₂) (G₂ * b₂ * M₂)
  generalize f (G₂ * b₁ * M₂) = a at r1 r2 hc1 hc2
  generalize f (G₂ * b₂ * b₁ * M₂) = b at r1 r2 hc1 hc3
  generalize f (G₂ * b₂ * M₂) = c at r1 r2 hc2 hc3
  generalize f Y = y at r1 ⊢
  generalize f 1 = o at r2 ⊢
  have hy : y = a * b⁻¹ * c := by
    calc y = (y * c⁻¹) * c := by group
      _ = a * b⁻¹ * c := by rw [← r1]
  have ho : o = c * b⁻¹ * a := by
    have : o⁻¹ = a⁻¹ * (b * c⁻¹) := by rw [r2]; group
    calc o = (o⁻¹)⁻¹ := by rw [inv_inv]
      _ = c * b⁻¹ * a := by rw [this]; group
  rw [hy, ho]
  have hb : b⁻¹ * c = c * b⁻¹ := by
    calc b⁻¹ * c = b⁻¹ * (c * b) * b⁻¹ := by group
      _ = b⁻¹ * (b * c) * b⁻¹ := by rw [hc3]
      _ = c * b⁻¹ := by group
  have ha : c * b⁻¹ * a = a * (c * b⁻¹) := by
    calc c * b⁻¹ * a = c * (b⁻¹ * a) := by group
      _ = c * (b⁻¹ * (a * b) * b⁻¹) := by group
      _ = c * (b⁻¹ * (b * a) * b⁻¹) := by rw [hc1]
      _ = c * a * b⁻¹ := by group
      _ = a * c * b⁻¹ := by rw [hc2]
      _ = a * (c * b⁻¹) := by group
  rw [ha, mul_assoc, hb]

end QuadA

end Setting4

end CFSG.Quasithin.H13.A6
