module

public import CFSG.Quasithin.H13.GoldschmidtM22CaseA3Aux

public section

namespace CFSG.Quasithin.H13.GM22.CaseA3

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G]

abbrev NV (V : Subgroup G) : Subgroup G := Subgroup.normalizer (V : Set G)

abbrev zs (T L V : Subgroup G) : Subgroup G :=
  V ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)

structure Setup (T L V D : Subgroup G) (z : G) (φ : ↥(NV V) →* Equiv.Perm (Fin 5)) : Prop where
  T_le : T ≤ NV V
  L_le : L ≤ NV V
  normalizes_L : NV V ≤ Subgroup.normalizer (L : Set G)
  V_le_T : V ≤ T
  V_le_L : V ≤ L
  isElemAbelian_V : IsElemAbelian 2 V
  isPGroup_T : IsPGroup 2 T
  odd_index_T : ¬ 2 ∣ (T.subgroupOf (NV V)).index
  ker_phi : ∀ x : ↥(NV V), φ x = 1 ↔ (x : G) ∈ V
  mem_L_iff : ∀ x : ↥(NV V), (x : G) ∈ L ↔ Equiv.Perm.sign (φ x) = 1
  centralizer_le : ∀ x ∈ NV V, x * z = z * x → x ∈ T
  transitive : ∀ v ∈ V, ∀ w ∈ V, v ≠ 1 → w ≠ 1 → ∃ l ∈ L, l * v * l⁻¹ = w
  z_mem : z ∈ V
  z_ne_one : z ≠ 1
  T_centralizes : ∀ t ∈ T, t * z = z * t
  eq_one_or_eq : ∀ u ∈ V, (∀ t ∈ T, t * u = u * t) → u = 1 ∨ u = z
  exists_zs : ∃ u ∈ zs T L V, u ≠ 1 ∧ u ≠ z
  card_zs : Nat.card ↥(zs T L V) = 4
  D_le_T : D ≤ T
  D_comm : ∀ x ∈ D, x * z = z * x
  card_D : Nat.card ↥D = 32
  not_D_le_L : ¬ D ≤ L
  card_V_inf_D : Nat.card ↥(V ⊓ D) = 8
  zs_le_D : zs T L V ≤ D

structure IsD0 (T L : Subgroup G) (z d₀ : G) : Prop where
  mem_L : d₀ ∈ L
  mem_normalizer : d₀ ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)
  prime : (orderOf d₀).Prime
  ne_two : orderOf d₀ ≠ 2
  moves : d₀ * z * d₀⁻¹ ≠ z

theorem comm_of_mem_zs {T L V : Subgroup G} {w u : G} (hw : w ∈ T ⊓ L) (hu : u ∈ zs T L V) :
    w * u = u * w :=
  Subgroup.mem_centralizer_iff.mp hu.2 w hw

namespace Setup

variable {T L V D : Subgroup G} {z : G} {φ : ↥(NV V) →* Equiv.Perm (Fin 5)}
  (C : Setup T L V D z φ)

include C in
theorem inv_mul_mem_L {t t' : G} (ht : t ∈ T) (ht' : t' ∈ T) (htL : t ∉ L) (ht'L : t' ∉ L) :
    t⁻¹ * t' ∈ L := by
  have hN := C.T_le ht
  have hN' := C.T_le ht'
  have h1 : Equiv.Perm.sign (φ ⟨t, hN⟩) = -1 :=
    (Int.units_eq_one_or _).resolve_left fun h => htL ((C.mem_L_iff ⟨t, hN⟩).mpr h)
  have h2 : Equiv.Perm.sign (φ ⟨t', hN'⟩) = -1 :=
    (Int.units_eq_one_or _).resolve_left fun h => ht'L ((C.mem_L_iff ⟨t', hN'⟩).mpr h)
  refine (C.mem_L_iff ⟨t⁻¹ * t', (NV V).mul_mem ((NV V).inv_mem hN) hN'⟩).mpr ?_
  have e : (⟨t⁻¹ * t', (NV V).mul_mem ((NV V).inv_mem hN) hN'⟩ : ↥(NV V)) =
      (⟨t, hN⟩ : ↥(NV V))⁻¹ * ⟨t', hN'⟩ := rfl
  rw [e, map_mul, map_inv, map_mul, map_inv, h1, h2]
  decide

include C in
theorem le_of_isPGroup [Finite G] {P : Subgroup G} (hPL : P ≤ L) (hP : IsPGroup 2 P)
    (hWP : T ⊓ L ≤ P) : P ≤ T ⊓ L := by
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf T (NV V) := ⟨C.T_le, C.isPGroup_T, C.odd_index_T⟩
  have := A4.isSylowTwoOf_inf_normal hS C.L_le C.normalizes_L
  exact (A4.isSylowTwoOf_iff_maximal.mp this).2.2 P hPL hP hWP

include C in
theorem z_mem_zs : z ∈ zs T L V :=
  ⟨C.z_mem, Subgroup.mem_centralizer_iff.mpr fun w hw => C.T_centralizes w hw.1⟩

include C in
theorem exists_d0 [Finite G] : ∃ d₀ : G, IsD0 T L z d₀ := by
  obtain ⟨z', hz'S, hz'1, hz'z⟩ := C.exists_zs
  obtain ⟨d', hd'L, hd'⟩ := C.transitive z C.z_mem z' hz'S.1 C.z_ne_one hz'1
  have hd'N : d' ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    refine CaseA3.mem_normalizer_of_conj_le fun x hx => ?_
    have hyL : d'⁻¹ * x * d' ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hd'L) hx.2) hd'L
    have hx' : x * z' = z' * x := comm_of_mem_zs hx hz'S
    have e1 : z = d'⁻¹ * z' * d' := by rw [← hd']; group
    have key : d'⁻¹ * x * d' * z = z * (d'⁻¹ * x * d') := by
      calc d'⁻¹ * x * d' * z = d'⁻¹ * (x * z') * d' := by rw [e1]; group
        _ = d'⁻¹ * (z' * x) * d' := by rw [hx']
        _ = z * (d'⁻¹ * x * d') := by rw [e1]; group
    exact ⟨C.centralizer_le _ (C.L_le hyL) key, hyL⟩
  have hW2 : IsPGroup 2 ↥(T ⊓ L) := C.isPGroup_T.to_le inf_le_left
  have hord : ∀ k : ℕ, orderOf d' ≠ 2 ^ k := by
    intro k hk
    have hd2 : IsPGroup 2 ↥(Subgroup.zpowers d') :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    have hjoin := CaseA3.isPGroup_sup_two (Subgroup.zpowers_le.mpr hd'N) hd2 hW2
    have hle := C.le_of_isPGroup (sup_le (Subgroup.zpowers_le.mpr hd'L) inf_le_right) hjoin
      le_sup_right
    have hd'W : d' ∈ T ⊓ L := hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers d'))
    apply hz'z
    rw [← hd', mul_inv_eq_iff_eq_mul]
    exact (C.T_centralizes d' hd'W.1)
  obtain ⟨p, hp, hp2, hordp⟩ := CaseA3.exists_odd_prime_order_pow hord
  refine ⟨d' ^ (orderOf d' / p), ⟨L.pow_mem hd'L _, Subgroup.pow_mem _ hd'N _,
    by rw [hordp]; exact hp, by rw [hordp]; exact hp2, fun hc => ?_⟩⟩
  have hd0T : d' ^ (orderOf d' / p) ∈ T :=
    C.centralizer_le _ (C.L_le (L.pow_mem hd'L _)) (mul_inv_eq_iff_eq_mul.mp hc)
  exact CaseA3.orderOf_ne_prime_of_isPGroup C.isPGroup_T hd0T hp hp2 hordp

end Setup

end CFSG.Quasithin.H13.GM22.CaseA3
