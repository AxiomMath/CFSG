module

public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

private theorem w16l_map_conjSubgroup_hom {G K : Type*} [Group G] [Group K]
    (f : G →* K) (A : Subgroup G) (x : G) :
    CFSG.Quasithin.conjSubgroup (A.map f) (f x) = (CFSG.Quasithin.conjSubgroup A x).map f := by
  rw [CFSG.Quasithin.conjSubgroup, CFSG.Quasithin.conjSubgroup, Subgroup.map_map,
    Subgroup.map_map]
  congr 1
  ext a
  simp [MulAut.conj_apply, map_mul]

private theorem w16l_mem_normalizer_sup_ker {G K : Type*} [Group G] [Group K]
    (f : G →* K) {A : Subgroup G} {b : G}
    (hb : f b ∈ Subgroup.normalizer ((A.map f : Subgroup K) : Set K)) :
    b ∈ Subgroup.normalizer ((A ⊔ f.ker : Subgroup G) : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff] at hb ⊢
  intro n
  rw [← Subgroup.comap_map_eq (f := f) A]
  constructor
  · intro hn
    refine Subgroup.mem_comap.mpr ?_
    have hn' : f n ∈ A.map f := Subgroup.mem_comap.mp hn
    rw [map_mul, map_mul, map_inv]
    exact (hb (f n)).mp hn'
  · intro hn
    refine Subgroup.mem_comap.mpr ((hb (f n)).mpr ?_)
    have hn' : f (b * n * b⁻¹) ∈ A.map f := Subgroup.mem_comap.mp hn
    rwa [map_mul, map_mul, map_inv] at hn'

private theorem w16l_conj_mem_of_mem_normalizer_sup {X : Type*} [Group X] [Finite X]
    {Z T : Subgroup X} (hZ : Z ≤ Subgroup.center X) (hZo : Odd (Nat.card Z))
    (hT : IsPGroup 2 T) {y : X}
    (hy : y ∈ Subgroup.normalizer ((T ⊔ Z : Subgroup X) : Set X)) :
    ∀ t ∈ T, y * t * y⁻¹ ∈ T := by
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  intro t ht
  have hmem : y * t * y⁻¹ ∈ ((T ⊔ Z : Subgroup X) : Set X) :=
    (Subgroup.mem_set_normalizer_iff.mp hy t).mp (Subgroup.mem_sup_left ht)
  rw [Subgroup.mul_normal T Z, Set.mem_mul] at hmem
  obtain ⟨a, ha, z, hz, haz⟩ := hmem
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by
    have := congr_arg (Subtype.val) hk
    simpa using this
  obtain ⟨j, hj⟩ := hT ⟨a, ha⟩
  have haj : a ^ 2 ^ j = 1 := by
    have := congr_arg (Subtype.val) hj
    simpa using this
  have hkm : k ≤ max k j := le_max_left k j
  have hjm : j ≤ max k j := le_max_right k j
  have htm : t ^ 2 ^ (max k j) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one] at htk ⊢
    exact htk.trans (pow_dvd_pow 2 hkm)
  have ham : a ^ 2 ^ (max k j) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one] at haj ⊢
    exact haj.trans (pow_dvd_pow 2 hjm)
  have hcomm : Commute a z := Subgroup.mem_center_iff.mp (hZ hz) a
  have hconj : (y * t * y⁻¹) ^ 2 ^ (max k j) = 1 := by
    rw [conj_pow, htm, mul_one, mul_inv_cancel]
  have hprod : (a * z) ^ 2 ^ (max k j) = 1 := by
    rw [haz]
    exact hconj
  have hzpow : z ^ 2 ^ (max k j) = 1 := by
    have hp : (a * z) ^ 2 ^ (max k j) = a ^ 2 ^ (max k j) * z ^ 2 ^ (max k j) :=
      hcomm.mul_pow _
    rw [hprod, ham, one_mul] at hp
    exact hp.symm
  have hzone : z = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes (a := 2 ^ max k j) (b := Nat.card Z) (k := orderOf z)
      ((hZo.coprime_two_left).pow_left _) (orderOf_dvd_iff_pow_eq_one.mpr hzpow)
      (Subgroup.orderOf_dvd_natCard Z hz)
  rw [hzone, mul_one] at haz
  rw [← haz]
  exact ha

theorem w16l_mem_normalizer_of_mem_normalizer_sup {X : Type*} [Group X] [Finite X]
    {Z T : Subgroup X} (hZ : Z ≤ Subgroup.center X) (hZo : Odd (Nat.card Z))
    (hT : IsPGroup 2 T) {y : X} (hy : y ∈ Subgroup.normalizer ((T ⊔ Z : Subgroup X) : Set X)) :
    y ∈ Subgroup.normalizer (T : Set X) := by
  haveI : Finite (T : Set X) := Finite.of_injective (Subtype.val) Subtype.val_injective
  exact Subgroup.mem_normalizer_fintype fun t ht =>
    w16l_conj_mem_of_mem_normalizer_sup hZ hZo hT hy t ht

theorem w16l_descent_free {X : Type*} [Group X] [Finite X] {B : Subgroup X}
    (hZo : Odd (Nat.card (Subgroup.center X))) (hB : IsPGroup 2 B) (x : X)
    (hfree : ∀ b ∈ B,
      b ∈ Subgroup.normalizer ((CFSG.Quasithin.conjSubgroup B x : Subgroup X) : Set X) → b = 1) :
    ∀ b ∈ B.map (QuotientGroup.mk' (Subgroup.center X)),
      b ∈ Subgroup.normalizer
        ((CFSG.Quasithin.conjSubgroup (B.map (QuotientGroup.mk' (Subgroup.center X)))
          (QuotientGroup.mk' (Subgroup.center X) x) : Subgroup (X ⧸ Subgroup.center X)) :
          Set (X ⧸ Subgroup.center X)) → b = 1 := by
  intro b hb hbn
  obtain ⟨b₀, hb₀B, hb₀eq⟩ := Subgroup.mem_map.mp hb
  rw [← hb₀eq] at hbn ⊢
  rw [w16l_map_conjSubgroup_hom (QuotientGroup.mk' (Subgroup.center X)) B x] at hbn
  have hker : (QuotientGroup.mk' (Subgroup.center X)).ker = Subgroup.center X :=
    QuotientGroup.ker_mk' (Subgroup.center X)
  have hb₀N : b₀ ∈ Subgroup.normalizer
      (((CFSG.Quasithin.conjSubgroup B x) ⊔
        (QuotientGroup.mk' (Subgroup.center X)).ker : Subgroup X) : Set X) :=
    w16l_mem_normalizer_sup_ker (QuotientGroup.mk' (Subgroup.center X)) hbn
  rw [hker] at hb₀N
  have hA2 : IsPGroup 2 (CFSG.Quasithin.conjSubgroup B x) := by
    change IsPGroup 2 (B.map (MulAut.conj x⁻¹).toMonoidHom)
    exact hB.map (MulAut.conj x⁻¹).toMonoidHom
  have hb₀mem : b₀ ∈ Subgroup.normalizer
      ((CFSG.Quasithin.conjSubgroup B x : Subgroup X) : Set X) :=
    w16l_mem_normalizer_of_mem_normalizer_sup le_rfl hZo hA2 hb₀N
  have hb₀one : b₀ = 1 := hfree b₀ hb₀B hb₀mem
  subst b₀
  simp

end CFSG.LocalAnalysis.WeakClosure81

end
