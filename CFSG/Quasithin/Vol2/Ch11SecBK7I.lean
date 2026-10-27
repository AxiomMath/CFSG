module

public import CFSG.Quasithin.Vol2.Ch11SecANat
public import CFSG.Quasithin.Vol2.Ch11SecBK7F

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (qSp)
open scoped IsMulCommutative

namespace K7

variable {K : Type} [Field K]

theorem qSp_fix_plane (x y z : K) {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ spPlane K) :
    mat 2 K (qSp x y z) *ᵥ v = v := by
  rw [qSp_mulVec]
  exact vec4_eq (by rw [vec4_apply_inl0, hv.1, hv.2]; ring)
    (by rw [vec4_apply_inl1, hv.1, hv.2]; ring) (by rw [vec4_apply_inr0]) (by rw [vec4_apply_inr1])

theorem y₀_ne_zero {k : Fin 2 ⊕ Fin 2 → K} (hk : k ∉ spPlane K) :
    vec4 (k (.inr 1)) (-k (.inr 0)) 0 0 ≠ 0 := by
  intro h
  apply hk
  refine ⟨?_, ?_⟩
  · have := congrFun h (.inl 1)
    rw [vec4_apply_inl1, Pi.zero_apply, neg_eq_zero] at this
    exact this
  · have := congrFun h (.inl 0)
    rwa [vec4_apply_inl0, Pi.zero_apply] at this

theorem exists_trv_of_qSp_fix [CharP K 2] {x y z : K} {k : Fin 2 ⊕ Fin 2 → K}
    (hk : k ∉ spPlane K) (hfix : mat 2 K (qSp x y z) *ᵥ k = k) :
    ∃ c : K, qSp x y z = trv (vec4 (k (.inr 1)) (-k (.inr 0)) 0 0) c :=
  eq_trv_of_fix (y₀_ne_zero hk) fun _ hv =>
    fix_perp_of_plane (fun _ hp => qSp_fix_plane x y z hp) hfix hk hv

section Index

variable {G : Type} [Group G] {V : Subgroup G} [IsMulCommutative ↥V]
  {H : Subgroup (MulAut ↥V)} {Z : Subgroup ↥V} {π : ↥(StatedSp 2 K) →* ↥H}
  {f : ↥V → (Fin 2 ⊕ Fin 2 → K)}

theorem relIndex_eq_card (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) {C : Subgroup G}
    {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0)
    (hC : ∀ v : ↥V, (v : G) ∈ C ↔ Matrix.toBilin' (spJ K) (f v) y = 0) :
    (V ⊓ C).relIndex V = Nat.card K := by
  let φ : ↥V →* Multiplicative K :=
    { toFun := fun v => Multiplicative.ofAdd (Matrix.toBilin' (spJ K) (f v) y)
      map_one' := by rw [hf.map_one, map_zero, LinearMap.zero_apply, ofAdd_zero]
      map_mul' := fun a b => by rw [hf.map_mul, bil_add_left, ofAdd_add] }
  have hker : φ.ker = (V ⊓ C).subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hC]
    exact ⟨fun h => ⟨v.2, ofAdd_eq_one.mp h⟩, fun h => ofAdd_eq_one.mpr h.2⟩
  have hsurj : Function.Surjective φ := by
    intro c
    obtain ⟨x, hx⟩ := exists_bil_eq_one hy
    obtain ⟨w, hw⟩ := hf.surj (Multiplicative.toAdd c • x)
    refine ⟨w, ?_⟩
    change Multiplicative.ofAdd (Matrix.toBilin' (spJ K) (f w) y) = c
    rw [hw, bil_smul_left, hx, mul_one, ofAdd_toAdd]
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj,
    Subgroup.card_top]
  rfl

theorem mQuot_eq_of_iff (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) {n : ℕ}
    (hK : Nat.card K = 2 ^ n) {C : Subgroup G} {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0)
    (hC : ∀ v : ↥V, (v : G) ∈ C ↔ Matrix.toBilin' (spJ K) (f v) y = 0) :
    E3.mQuot V (V ⊓ C) = n := by
  rw [E3.mQuot, relIndex_eq_card hf hy hC, hK, padicValNat.prime_pow]

end Index

variable {G : Type} [Group G]

theorem card_autOn_eq_two_pow [Finite G] {A V : Subgroup G} (hA : IsPGroup 2 A)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) {m : ℕ}
    (hm : E3.mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) = m) :
    Nat.card (autOn A V) = 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (B6.isPGroup_autOn hA V)
  rw [E3.mQuot, ← card_autOn_eq_relIndex hAV, hk, padicValNat.prime_pow] at hm
  rw [hk, hm]

theorem conjV_comm_mem {V E : Subgroup G} {e : G} (he : e ∈ E)
    (heV : e ∈ Subgroup.normalizer (V : Set G)) (v : ↥V) :
    ((SecA.conjV V e heV v * v⁻¹ : ↥V) : G) ∈ ⁅V, E⁆ := by
  rw [Subgroup.commutator_comm]
  have := Subgroup.commutator_mem_commutator he v.2
  rwa [commutatorElement_def, ← SecA.conjV_apply_coe V heV v] at this

theorem le_commutator_of_le_acomm {L V E : Subgroup G} {U : Subgroup ↥V}
    (hZU : (Subgroup.centralizer (L : Set G)).subgroupOf V ≤ U)
    (hU : U ≤ (⁅V, E⁆).subgroupOf V) : V ⊓ Subgroup.centralizer (L : Set G) ≤ ⁅V, E⁆ :=
  fun z hz => hU (hZU (show (⟨z, hz.1⟩ : ↥V) ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V
    from hz.2))

end K7

end CFSG.Quasithin.Vol2.Ch11.SecB
