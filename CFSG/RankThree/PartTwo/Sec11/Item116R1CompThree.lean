module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1Comp
public import CFSG.RankThree.PartTwo.Sec11.Item116R1Lift
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.GroupTheory.ThompsonAxB
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

@[expose] def SuzukiAutFacts : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsKGroup X → ∀ (J : Subgroup X), IsSimpleGroup ↥J → Group.IsPerfect ↥J →
    ¬ 3 ∣ Nat.card J → ∀ y ∈ Subgroup.normalizer (J : Set X), y ^ 3 ∈ Subgroup.centralizer (J : Set X) →
      (∃ e ∈ J, e ≠ 1 ∧ y * e = e * y) ∧
      (∀ N : Subgroup X, N ≤ J → IsPGroup 2 N → (∀ n ∈ N, y * n = n * y) →
        (∀ f ∈ J, y * f = f * y → ∀ n ∈ N, f * n * f⁻¹ ∈ N) → N = ⊥) ∧
      (∀ x ∈ Subgroup.normalizer (J : Set X), x * y = y * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
        (∀ j ∈ J, y * j = j * y → x * j = j * x) → ∀ j ∈ J, x * j = j * x)

@[expose] def IsCoord {X : Type*} [Group X] (J : Subgroup X) (g j : X) : Prop :=
  j ∈ J ∧ ∀ k ∈ J, (j⁻¹ * g) * k = k * (j⁻¹ * g)

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

section CoordAlgebra

variable {X : Type*} [Group X] {J : Subgroup X} {g g' j j' : X}

theorem isCoord_mul (h : IsCoord J g j) (h' : IsCoord J g' j') : IsCoord J (g * g') (j * j') := by
  unfold IsCoord at h h' ⊢
  obtain ⟨hj, hc⟩ := h
  obtain ⟨hj', hc'⟩ := h'
  refine ⟨J.mul_mem hj hj', fun k hk => ?_⟩
  have hm : (j * j')⁻¹ * (g * g') = (j⁻¹ * g) * (j'⁻¹ * g') := by
    calc (j * j')⁻¹ * (g * g') = j'⁻¹ * ((j⁻¹ * g) * g') := by group
      _ = j'⁻¹ * ((j⁻¹ * g) * (j' * (j'⁻¹ * g'))) := by group
      _ = j'⁻¹ * (((j⁻¹ * g) * j') * (j'⁻¹ * g')) := by simp only [mul_assoc]
      _ = j'⁻¹ * ((j' * (j⁻¹ * g)) * (j'⁻¹ * g')) := by rw [hc j' hj']
      _ = (j⁻¹ * g) * (j'⁻¹ * g') := by group
  rw [hm]
  calc (j⁻¹ * g) * (j'⁻¹ * g') * k = (j⁻¹ * g) * ((j'⁻¹ * g') * k) := by simp only [mul_assoc]
    _ = (j⁻¹ * g) * (k * (j'⁻¹ * g')) := by rw [hc' k hk]
    _ = ((j⁻¹ * g) * k) * (j'⁻¹ * g') := by simp only [mul_assoc]
    _ = (k * (j⁻¹ * g)) * (j'⁻¹ * g') := by rw [hc k hk]
    _ = k * ((j⁻¹ * g) * (j'⁻¹ * g')) := by simp only [mul_assoc]

theorem isCoord_inv (h : IsCoord J g j) : IsCoord J g⁻¹ j⁻¹ := by
  unfold IsCoord at h ⊢
  obtain ⟨hj, hc⟩ := h
  have hjg : Commute j g := by
    show j * g = g * j
    calc j * g = j * (j * (j⁻¹ * g)) := by group
      _ = j * ((j⁻¹ * g) * j) := by rw [hc j hj]
      _ = (j * (j⁻¹ * g)) * j := by simp only [mul_assoc]
      _ = g * j := by group
  refine ⟨J.inv_mem hj, fun k hk => ?_⟩
  have hinv : (j⁻¹)⁻¹ * g⁻¹ = (j⁻¹ * g)⁻¹ := by
    rw [mul_inv_rev, inv_inv]
    exact hjg.inv_right
  rw [hinv]
  exact (show Commute (j⁻¹ * g) k from hc k hk).inv_left

theorem isCoord_self (hj : j ∈ J) : IsCoord J j j := by
  unfold IsCoord
  refine ⟨hj, fun k _ => ?_⟩
  simp

theorem isCoord_one_of_centralizes (he : ∀ k ∈ J, g * k = k * g) : IsCoord J g 1 := by
  unfold IsCoord
  refine ⟨J.one_mem, fun k hk => ?_⟩
  simpa using he k hk

theorem isCoord_one_one : IsCoord J (1 : X) 1 := by
  unfold IsCoord
  refine ⟨J.one_mem, fun k _ => ?_⟩
  simp

theorem isCoord_conj (u : X) (h : IsCoord J g j) :
    IsCoord (J.map (MulAut.conj u).toMonoidHom) (u * g * u⁻¹) (u * j * u⁻¹) := by
  unfold IsCoord at h ⊢
  obtain ⟨hj, hc⟩ := h
  refine ⟨Subgroup.mem_map.mpr ⟨j, hj, rfl⟩, fun k' hk' => ?_⟩
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hk'
  have e1 : (u * j * u⁻¹)⁻¹ * (u * g * u⁻¹) = u * (j⁻¹ * g) * u⁻¹ := by group
  show ((u * j * u⁻¹)⁻¹ * (u * g * u⁻¹)) * (u * k * u⁻¹) =
    (u * k * u⁻¹) * ((u * j * u⁻¹)⁻¹ * (u * g * u⁻¹))
  rw [e1]
  calc u * (j⁻¹ * g) * u⁻¹ * (u * k * u⁻¹) = u * ((j⁻¹ * g) * k) * u⁻¹ := by group
    _ = u * (k * (j⁻¹ * g)) * u⁻¹ := by rw [hc k hk]
    _ = u * k * u⁻¹ * (u * (j⁻¹ * g) * u⁻¹) := by group

theorem isCoord_unique (hZ : Subgroup.center J = ⊥) (h : IsCoord J g j) (h' : IsCoord J g j') :
    j = j' := by
  unfold IsCoord at h h'
  obtain ⟨hj, hc⟩ := h
  obtain ⟨hj', hc'⟩ := h'
  have hmem : j⁻¹ * j' ∈ J := J.mul_mem (J.inv_mem hj) hj'
  have hz : (⟨j⁻¹ * j', hmem⟩ : J) ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have hk1 : Commute (j⁻¹ * g) (k : X) := hc _ k.2
    have hk2 : Commute (j'⁻¹ * g) (k : X) := hc' _ k.2
    have hcomm : Commute (j⁻¹ * g * (j'⁻¹ * g)⁻¹) (k : X) := hk1.mul_left hk2.inv_left
    have heq : j⁻¹ * g * (j'⁻¹ * g)⁻¹ = j⁻¹ * j' := by group
    rw [heq] at hcomm
    exact hcomm.symm
  rw [hZ] at hz
  have h1 : (⟨j⁻¹ * j', hmem⟩ : J) = 1 := Subgroup.mem_bot.mp hz
  have h2 : j⁻¹ * j' = 1 := congrArg Subtype.val h1
  exact inv_mul_eq_one.mp h2

theorem isCoord_pow (n : ℕ) (h : IsCoord J g j) : IsCoord J (g ^ n) (j ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact isCoord_one_one
  | succ n ih =>
    simp only [pow_succ]
    exact isCoord_mul ih h

end CoordAlgebra

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

section Layer

variable {X : Type*} [Group X] [Finite X]

theorem exists_isCoord_of_mem_layer {J : Subgroup X} (hJ : CFSG.IsComponent J) {g : X}
    (hg : g ∈ CFSG.layer X) : ∃ j, IsCoord J g j := by
  obtain ⟨x, hx⟩ := CFSG.LocalCores.exists_layerMul_eq hg
  refine ⟨(x ⟨J, hJ⟩ : X), ?_⟩
  unfold IsCoord
  refine ⟨(x ⟨J, hJ⟩).2, fun k hk => ?_⟩
  have hu := CFSG.LocalCores.layerMul_eq_mul_update x ⟨J, hJ⟩
  have hc := CFSG.LocalCores.commute_layerMul_update x ⟨J, hJ⟩ hk
  rw [← hx, hu, inv_mul_cancel_left]
  exact hc.symm.eq

theorem eq_one_of_forall_isCoord_one (hZ : ∀ J : Subgroup X, CFSG.IsComponent J → Subgroup.center J = ⊥)
    {g : X} (hg : g ∈ CFSG.layer X) (h : ∀ J : Subgroup X, CFSG.IsComponent J → IsCoord J g 1) :
    g = 1 := by
  have hle : CFSG.layer X ≤ Subgroup.centralizer ({g} : Set X) := by
    rw [CFSG.layer.eq_sSup]
    refine sSup_le fun L hL => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨_, hc⟩ := h L hL
    have hc' := hc y hy
    simp only [inv_one, one_mul] at hc'
    exact hc'.symm
  have hgc : g ∈ Subgroup.centralizer (CFSG.layer X : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  obtain ⟨x, rfl⟩ := CFSG.LocalCores.exists_layerMul_eq hg
  have hx1 : ∀ K : CFSG.LocalCores.ComponentIndex X, x K = 1 := by
    intro K
    have hK := (CFSG.LocalCores.layerMul_mem_centralizer_iff x).mp hgc K
    rw [hZ K.1 K.2] at hK
    exact Subgroup.mem_bot.mp hK
  have hx : x = 1 := by
    funext K
    exact hx1 K
  rw [hx, map_one]

theorem component_center_bot_of_prime_three
    (hθ : aschbacherSolvableCore 3 X = ⊥) {J : Subgroup X} (hJ : CFSG.IsComponent J)
    (h3 : ¬ 3 ∣ Nat.card J) : Subgroup.center J = ⊥ := by
  have hZ : (Subgroup.center J).map J.subtype ≤ CFSG.pCore 3 X :=
    (CFSG.LocalCores.center_component_le_center_layer hJ).trans
      ((CFSG.WholeGroup.center_layer_le_fittingSubgroup (G := X)).trans
        (compT_fitting_le_pCore_three hθ))
  have hP : IsPGroup 3 (Subgroup.center J) := by
    intro g
    obtain ⟨k, hk⟩ := compT_pow_eq_one_of_mem_pCore 3
      (hZ (Subgroup.mem_map_of_mem J.subtype g.2))
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using hk))⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have hdvd : Nat.card (Subgroup.center J) ∣ Nat.card J :=
    Subgroup.card_subgroup_dvd_card (Subgroup.center J)
  rw [hn] at hdvd
  have hn0 : n = 0 := by
    by_contra hne
    exact h3 ((dvd_pow_self 3 hne).trans hdvd)
  rw [hn0, pow_zero] at hn
  exact Subgroup.eq_bot_of_card_eq _ hn

end Layer

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

variable {X : Type*} [Group X]

theorem ct2_mem_map_conj {K : Subgroup X} {g m : X} :
    m ∈ K.map (MulAut.conj g).toMonoidHom ↔ ∃ k ∈ K, g * k * g⁻¹ = m := by
  simp [Subgroup.mem_map, MulAut.conj_apply]

theorem ct2_map_map (g a : X) (K : Subgroup X) :
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      K.map (MulAut.conj (g * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [MulAut.conj_apply, mul_assoc]

theorem ct2_map_one (K : Subgroup X) : K.map (MulAut.conj (1 : X)).toMonoidHom = K := by
  ext m
  rw [ct2_mem_map_conj]
  simp

theorem ct2_stab_mul {K : Subgroup X} {g h : X}
    (hg : K.map (MulAut.conj g).toMonoidHom = K) (hh : K.map (MulAut.conj h).toMonoidHom = K) :
    K.map (MulAut.conj (g * h)).toMonoidHom = K := by
  rw [← ct2_map_map, hh, hg]

theorem ct2_stab_pow {K : Subgroup X} {g : X}
    (hg : K.map (MulAut.conj g).toMonoidHom = K) (j : ℕ) :
    K.map (MulAut.conj (g ^ j)).toMonoidHom = K := by
  induction j with
  | zero => rw [pow_zero]; exact ct2_map_one K
  | succ j ih => rw [pow_succ]; exact ct2_stab_mul ih hg

theorem ct2_sq_sq_eq {y : X} (hy3 : y ^ 3 = 1) : y ^ 2 * y ^ 2 = y := by
  calc y ^ 2 * y ^ 2 = y * y ^ 3 := by group
    _ = y := by rw [hy3, mul_one]

theorem ct2_sq_sq_eq' {y : X} (hy3 : y ^ 3 = 1) : (y ^ 2) ^ 2 = y := by
  calc (y ^ 2) ^ 2 = y * y ^ 3 := by group
    _ = y := by rw [hy3, mul_one]

theorem ct2_sq_mul_eq {y : X} (hy3 : y ^ 3 = 1) : y ^ 2 * y = 1 := by
  calc y ^ 2 * y = y ^ 3 := by group
    _ = 1 := hy3

theorem ct2_mul_sq_eq {y : X} (hy3 : y ^ 3 = 1) : y * y ^ 2 = 1 := by
  calc y * y ^ 2 = y ^ 3 := by group
    _ = 1 := hy3

theorem ct2_stab_of_sq {K : Subgroup X} {y : X} (hy3 : y ^ 3 = 1)
    (h : K.map (MulAut.conj (y ^ 2)).toMonoidHom = K) :
    K.map (MulAut.conj y).toMonoidHom = K := by
  have h1 := ct2_stab_mul h h
  rwa [ct2_sq_sq_eq hy3] at h1

theorem ct2_pow_two_pow {y : X} (hy3 : y ^ 3 = 1) (m : ℕ) :
    y ^ (2 ^ m) = y ∨ y ^ (2 ^ m) = y ^ 2 := by
  induction m with
  | zero => left; simp
  | succ m ih =>
    rw [pow_succ (2 : ℕ) m, pow_mul y (2 ^ m) 2]
    rcases ih with h | h
    · right; rw [h]
    · left; rw [h, ct2_sq_sq_eq' hy3]

theorem ct2_comm3 {a b k : X} (h12 : k * a = a * k) (h13 : k * b = b * k) :
    a * b * k = k * a * b := by
  calc a * b * k = a * (b * k) := mul_assoc a b k
    _ = a * (k * b) := by rw [h13]
    _ = a * k * b := (mul_assoc a k b).symm
    _ = k * a * b := by rw [h12]

theorem ct2_coord_aux {a b k : X} (ha : a * k = k * a) (hb : b * k = k * b) :
    a * b * k = k * (a * b) := by
  calc a * b * k = a * (b * k) := mul_assoc a b k
    _ = a * (k * b) := by rw [hb]
    _ = a * k * b := (mul_assoc a k b).symm
    _ = k * a * b := by rw [ha]
    _ = k * (a * b) := mul_assoc k a b

theorem ct2_conj_aux {x g k : X} (h : x * g = g * x) :
    x * (g * k * g⁻¹) * x⁻¹ = g * (x * k * x⁻¹) * g⁻¹ := by
  calc x * (g * k * g⁻¹) * x⁻¹ = (x * g) * k * (x * g)⁻¹ := by group
    _ = (g * x) * k * (g * x)⁻¹ := by rw [h]
    _ = g * (x * k * x⁻¹) * g⁻¹ := by group

theorem map_conj_sq_ne {K : Subgroup X} {y : X} (hy3 : y ^ 3 = 1)
    (hK : K.map (MulAut.conj y).toMonoidHom ≠ K) :
    K.map (MulAut.conj (y ^ 2)).toMonoidHom ≠ K ∧
    K.map (MulAut.conj (y ^ 2)).toMonoidHom ≠ K.map (MulAut.conj y).toMonoidHom := by
  refine ⟨fun h => hK (ct2_stab_of_sq hy3 h), fun h => hK ?_⟩
  calc K.map (MulAut.conj y).toMonoidHom
      = K.map (MulAut.conj (y ^ 2 * y ^ 2)).toMonoidHom := by rw [ct2_sq_sq_eq hy3]
    _ = (K.map (MulAut.conj (y ^ 2)).toMonoidHom).map (MulAut.conj (y ^ 2)).toMonoidHom :=
        (ct2_map_map _ _ _).symm
    _ = (K.map (MulAut.conj y).toMonoidHom).map (MulAut.conj (y ^ 2)).toMonoidHom := by rw [h]
    _ = K.map (MulAut.conj (y ^ 2 * y)).toMonoidHom := ct2_map_map _ _ _
    _ = K.map (MulAut.conj 1).toMonoidHom := by rw [ct2_sq_mul_eq hy3]
    _ = K := ct2_map_one K

@[expose] def diag3 (y k : X) : X := k * (y * k * y⁻¹) * (y ^ 2 * k * (y ^ 2)⁻¹)

theorem diag3_comm {y k : X} (hy3 : y ^ 3 = 1)
    (h12 : k * (y * k * y⁻¹) = (y * k * y⁻¹) * k)
    (h13 : k * (y ^ 2 * k * (y ^ 2)⁻¹) = (y ^ 2 * k * (y ^ 2)⁻¹) * k)
    (h23 : (y * k * y⁻¹) * (y ^ 2 * k * (y ^ 2)⁻¹) = (y ^ 2 * k * (y ^ 2)⁻¹) * (y * k * y⁻¹)) :
    y * diag3 y k = diag3 y k * y := by
  have hA : y * (y * k * y⁻¹) * y⁻¹ = y ^ 2 * k * (y ^ 2)⁻¹ := by
    simp only [pow_two, mul_inv_rev, mul_assoc]
  have hB : y * (y ^ 2 * k * (y ^ 2)⁻¹) * y⁻¹ = k := by
    calc y * (y ^ 2 * k * (y ^ 2)⁻¹) * y⁻¹ = y ^ 3 * k * (y ^ 3)⁻¹ := by group
      _ = k := by rw [hy3, inv_one, one_mul, mul_one]
  have hyD : y * diag3 y k * y⁻¹ = diag3 y k := by
    unfold diag3
    calc y * (k * (y * k * y⁻¹) * (y ^ 2 * k * (y ^ 2)⁻¹)) * y⁻¹
        = (y * k * y⁻¹) * (y * (y * k * y⁻¹) * y⁻¹) * (y * (y ^ 2 * k * (y ^ 2)⁻¹) * y⁻¹) := by
          group
      _ = (y * k * y⁻¹) * (y ^ 2 * k * (y ^ 2)⁻¹) * k := by rw [hA, hB]
      _ = k * (y * k * y⁻¹) * (y ^ 2 * k * (y ^ 2)⁻¹) := ct2_comm3 h12 h13
  calc y * diag3 y k = (y * diag3 y k * y⁻¹) * y := by group
    _ = diag3 y k * y := by rw [hyD]

theorem isCoord_diag3 {K : Subgroup X} {y k : X} (hk : k ∈ K)
    (h2 : ∀ m ∈ K.map (MulAut.conj y).toMonoidHom, ∀ k' ∈ K, m * k' = k' * m)
    (h3 : ∀ m ∈ K.map (MulAut.conj (y ^ 2)).toMonoidHom, ∀ k' ∈ K, m * k' = k' * m) :
    IsCoord K (diag3 y k) k := by
  have ha : y * k * y⁻¹ ∈ K.map (MulAut.conj y).toMonoidHom := ct2_mem_map_conj.2 ⟨k, hk, rfl⟩
  have hb : y ^ 2 * k * (y ^ 2)⁻¹ ∈ K.map (MulAut.conj (y ^ 2)).toMonoidHom :=
    ct2_mem_map_conj.2 ⟨k, hk, rfl⟩
  have hcancel : k⁻¹ * diag3 y k = y * k * y⁻¹ * (y ^ 2 * k * (y ^ 2)⁻¹) := by
    unfold diag3
    group
  unfold IsCoord
  refine ⟨hk, fun k' hk' => ?_⟩
  rw [hcancel]
  exact ct2_coord_aux (h2 _ ha k' hk') (h3 _ hb k' hk')

theorem conj_diag3 {x y k : X} (hxy : x * y = y * x) :
    x * diag3 y k * x⁻¹ = diag3 y (x * k * x⁻¹) := by
  have hc : Commute x y := hxy
  have hxy2 : x * y ^ 2 = y ^ 2 * x := (hc.pow_right 2).eq
  unfold diag3
  calc x * (k * (y * k * y⁻¹) * (y ^ 2 * k * (y ^ 2)⁻¹)) * x⁻¹
      = (x * k * x⁻¹) * (x * (y * k * y⁻¹) * x⁻¹) * (x * (y ^ 2 * k * (y ^ 2)⁻¹) * x⁻¹) := by
        group
    _ = (x * k * x⁻¹) * (y * (x * k * x⁻¹) * y⁻¹) * (y ^ 2 * (x * k * x⁻¹) * (y ^ 2)⁻¹) := by
        rw [ct2_conj_aux hxy, ct2_conj_aux hxy2]

theorem conj_eq_of_orbit {K : Subgroup X} {x y : X} (hy3 : y ^ 3 = 1) (hxy : x * y = y * x)
    (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1) (hK : K.map (MulAut.conj y).toMonoidHom ≠ K)
    (h : K.map (MulAut.conj x).toMonoidHom = K ∨
      K.map (MulAut.conj x).toMonoidHom = K.map (MulAut.conj y).toMonoidHom ∨
      K.map (MulAut.conj x).toMonoidHom = K.map (MulAut.conj (y ^ 2)).toMonoidHom) :
    K.map (MulAut.conj x).toMonoidHom = K := by
  obtain ⟨n, hn⟩ := hx2
  have hc : Commute x y := hxy
  have hyx : Commute y x := hc.symm
  have hy_inv : y ^ 2 * y = 1 := ct2_sq_mul_eq hy3
  have hy_inv' : y * y ^ 2 = 1 := ct2_mul_sq_eq hy3
  have hy4 : (y ^ 2) ^ 2 = y := ct2_sq_sq_eq' hy3
  rcases h with h1 | h2 | h3
  · exact h1
  · exfalso
    have hw : K.map (MulAut.conj (y ^ 2 * x)).toMonoidHom = K := by
      rw [← ct2_map_map, h2, ct2_map_map, hy_inv, ct2_map_one]
    have hpow := ct2_stab_pow hw (2 ^ n)
    rw [(hyx.pow_left 2).mul_pow, hn, mul_one, pow_right_comm y 2 (2 ^ n)] at hpow
    rcases ct2_pow_two_pow hy3 n with h' | h'
    · rw [h'] at hpow
      exact hK (ct2_stab_of_sq hy3 hpow)
    · rw [h', hy4] at hpow
      exact hK hpow
  · exfalso
    have hw : K.map (MulAut.conj (y * x)).toMonoidHom = K := by
      rw [← ct2_map_map, h3, ct2_map_map, hy_inv', ct2_map_one]
    have hpow := ct2_stab_pow hw (2 ^ n)
    rw [hyx.mul_pow, hn, mul_one] at hpow
    rcases ct2_pow_two_pow hy3 n with h' | h'
    · rw [h'] at hpow
      exact hK hpow
    · rw [h'] at hpow
      exact hK (ct2_stab_of_sq hy3 hpow)

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

variable {X : Type*} [Group X] [Finite X]

theorem ct1a_axb {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P R B : Subgroup G) (hP : IsPGroup p P) (hR : Nat.Coprime (Nat.card R) p) (hB : IsPGroup p B)
    (hRP : R ≤ Subgroup.normalizer (P : Set G)) (hBP : B ≤ Subgroup.normalizer (P : Set G))
    (hRB : ⁅R, B⁆ = ⊥)
    (hfix : P ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (R : Set G)) :
    P ≤ Subgroup.centralizer (R : Set G) := by
  have hRB' : R ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRB
  let α : R →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hRP)
  let β : B →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hBP)
  have hα : ∀ (r : R) (x : P), ((α r x : P) : G) = r * x * (r : G)⁻¹ := fun r x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe P (Subgroup.inclusion hRP r) x
  have hβ : ∀ (b : B) (x : P), ((β b x : P) : G) = b * x * (b : G)⁻¹ := fun b x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe P (Subgroup.inclusion hBP b) x
  have hcomm : ∀ r b, α r * β b = β b * α r := by
    intro r b
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have hrb : (b : G) * r = r * b := Subgroup.mem_centralizer_iff.mp (hRB' r.2) b b.2
    rw [MulAut.mul_apply, MulAut.mul_apply, hα, hβ, hβ, hα]
    calc (r : G) * (b * x * (b : G)⁻¹) * (r : G)⁻¹ = (r * b) * x * ((r : G) * b)⁻¹ := by
          group
      _ = (b * r) * x * ((b : G) * r)⁻¹ := by rw [hrb]
      _ = b * (r * x * (r : G)⁻¹) * (b : G)⁻¹ := by group
  have hfix' : ∀ r x, (∀ b, β b x = x) → α r x = x := by
    intro r x hx
    have hxB : (x : G) ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h := congrArg Subtype.val (hx ⟨b, hb⟩)
      rw [hβ] at h
      calc b * (x : G) = b * x * b⁻¹ * b := by group
        _ = x * b := by rw [h]
    have hrx : (r : G) * x = x * r :=
      Subgroup.mem_centralizer_iff.mp (hfix ⟨x.2, hxB⟩) r r.2
    apply Subtype.ext
    rw [hα, hrx, mul_inv_cancel_right]
  have hR' : ¬ p ∣ Nat.card R :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hR.symm
  have key := CFSG.GroupTheory.thompson_A_times_B hP hR' hB α β hcomm hfix'
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have h := congrArg (fun f : MulAut P => ((f ⟨x, hx⟩ : P) : G)) (key ⟨r, hr⟩)
  simp only [hα, MulAut.one_apply] at h
  calc r * x = r * x * r⁻¹ * r := by group
    _ = x * r := by rw [h]

theorem ct1a_isPGroup_zpowers {G : Type*} [Group G] [Finite G] {b : G} (hb3 : b ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers b) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hb3) with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem ct1a_le_centralizer_zpowers {G : Type*} [Group G] {b : G} {Q : Subgroup G}
    (hQb : Q ≤ Subgroup.centralizer ({b} : Set G)) :
    Q ≤ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  rintro h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have hxb : Commute b x := (Subgroup.mem_centralizer_singleton_iff.mp (hQb hx)).symm
  exact (hxb.zpow_left k).eq

theorem pCore_two_centralizer_le_centralizer_pCore_three {y : X} (hy3 : y ^ 3 = 1) :
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set X)) ≤
      Subgroup.centralizer ((CFSG.pCore 3 X : Subgroup X) : Set X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ2 : IsPGroup 2 (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set X))) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.isPGroup_inSubgroup_pCore 2 _
  have hZcop : Nat.Coprime
      (Nat.card (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set X)))) 3 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hZ2
    rw [hn]
    exact Nat.Coprime.pow_left n (by norm_num)
  have hPp : IsPGroup 3 (CFSG.pCore 3 X) := CFSG.pCore_isPGroup
  have hPn : (CFSG.pCore 3 X).Normal := CFSG.pCore_normal
  have hPN : ∀ H : Subgroup X, H ≤ Subgroup.normalizer ((CFSG.pCore 3 X : Subgroup X) : Set X) := by
    intro H
    rw [Subgroup.normalizer_eq_top_iff.mpr hPn]
    exact le_top
  have hB : IsPGroup 3 (Subgroup.zpowers y) := ct1a_isPGroup_zpowers hy3
  have hZC : inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set X)) ≤
      Subgroup.centralizer ({y} : Set X) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_le 2 _
  have hRB : ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set X)),
      Subgroup.zpowers y⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (ct1a_le_centralizer_zpowers hZC)
  have hfix : CFSG.pCore 3 X ⊓ Subgroup.centralizer (Subgroup.zpowers y : Set X) ≤
      Subgroup.centralizer
        ((inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set X)) : Subgroup X) : Set X) := by
    rintro r ⟨hrO, hrB⟩
    have hry : r ∈ Subgroup.centralizer ({y} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hrB y (Subgroup.mem_zpowers y)).symm
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hn' : n ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set X)) := hn
    have hcP : n * r * n⁻¹ * r⁻¹ ∈ CFSG.pCore 3 X :=
      mul_mem (hPn.conj_mem r hrO n) (inv_mem hrO)
    have hcZ : n * r * n⁻¹ * r⁻¹ ∈
        inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set X)) := by
      have hrN := compJ1_le_normalizer_inSubgroup_pCore 2
        (Subgroup.centralizer ({y} : Set X)) hry
      have h2 : r * n⁻¹ * r⁻¹ ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set X)) :=
        (Subgroup.mem_normalizer_iff.mp hrN n⁻¹).mp (inv_mem hn')
      have h3 : n * r * n⁻¹ * r⁻¹ = n * (r * n⁻¹ * r⁻¹) := by group
      rw [h3]
      exact mul_mem hn' h2
    have hinf : inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set X)) ⊓
        CFSG.pCore 3 X = ⊥ :=
      compT_inf_eq_bot_of_pow (fun x hx => compT_pow_eq_one_of_mem_inSubgroup 2 hx)
        (fun x hx => compT_pow_eq_one_of_mem_pCore 3 hx)
    have hmem : n * r * n⁻¹ * r⁻¹ ∈
        inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set X)) ⊓ CFSG.pCore 3 X :=
      Subgroup.mem_inf.mpr ⟨hcZ, hcP⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    calc n * r = (n * r * n⁻¹ * r⁻¹) * (r * n) := by group
      _ = r * n := by rw [hmem, one_mul]
  have key := ct1a_axb (CFSG.pCore 3 X)
    (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set X)))
    (Subgroup.zpowers y) hPp hZcop hB (hPN _) (hPN _) hRB hfix
  exact Subgroup.le_centralizer_iff.mp key

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

variable {X : Type*} [Group X] [Finite X]

theorem eq_one_of_centralizes_layer_pCore_three
    (hθ : aschbacherSolvableCore 3 X = ⊥)
    {x : X} (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hL : ∀ e ∈ CFSG.layer X, x * e = e * x)
    (hO : ∀ o ∈ CFSG.pCore 3 X, x * o = o * x) : x = 1 := by
  obtain ⟨k, hk⟩ := hx2
  have hF : CFSG.fittingSubgroup X ≤ CFSG.pCore 3 X := compT_fitting_le_pCore_three hθ
  have hO2 : CFSG.pCore 2 X = ⊥ := compT_pCore_eq_bot_of_theta hθ Nat.prime_two (by norm_num)
  have hFc : CFSG.fittingSubgroup X ≤ Subgroup.centralizer ({x} : Set X) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact hO f (hF hf)
  have hLc : CFSG.layer X ≤ Subgroup.centralizer ({x} : Set X) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact hL e he
  have hMc : CFSG.generalizedFitting X ≤ Subgroup.centralizer ({x} : Set X) := by
    rw [CFSG.generalizedFitting.eq_sup X]
    exact sup_le hFc hLc
  have hx_cent : x ∈ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    exact ((Subgroup.mem_centralizer_iff.mp (hMc hm)) x (Set.mem_singleton x)).symm
  have hxM : x ∈ CFSG.generalizedFitting X := CFSG.centralizer_generalizedFitting_le X hx_cent
  have hIM : Subgroup.zpowers x ≤ CFSG.generalizedFitting X := Subgroup.zpowers_le.mpr hxM
  have hI_cent : Subgroup.zpowers x ≤ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) :=
    Subgroup.zpowers_le.mpr hx_cent
  have hIc : ∀ i ∈ Subgroup.zpowers x, ∀ m ∈ CFSG.generalizedFitting X, m * i = i * m :=
    fun i hi m hm => Subgroup.mem_centralizer_iff.mp (hI_cent hi) m hm
  have hI2 : ∀ i ∈ Subgroup.zpowers x, ∃ l : ℕ, i ^ 2 ^ l = 1 := by
    intro i hi
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hi
    refine ⟨k, ?_⟩
    rw [← zpow_natCast (x ^ n) (2 ^ k), ← zpow_mul, mul_comm n, zpow_mul, zpow_natCast, hk, one_zpow]
  have hbot : Subgroup.zpowers x = ⊥ :=
    compT_eq_bot_of_two_central (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
      hIM hIc hI2 hO2
  have hxb : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
  rw [hbot, Subgroup.mem_bot] at hxb
  exact hxb

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

section Helpers

variable {Y : Type*} [Group Y]

theorem ct3_comm {A B : Subgroup Y} (h : ⁅A, B⁆ = ⊥) {a b : Y} (ha : a ∈ A) (hb : b ∈ B) :
    a * b = b * a := by
  have h1 : ⁅a, b⁆ ∈ ⁅A, B⁆ := Subgroup.commutator_mem_commutator ha hb
  rw [h, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

def ct3_coordSub (W K : Subgroup Y) : Subgroup Y where
  carrier := {j | ∃ w ∈ W, IsCoord K w j}
  one_mem' := ⟨1, W.one_mem, isCoord_one_one⟩
  mul_mem' := by
    rintro a b ⟨w, hw, hwa⟩ ⟨w', hw', hwb⟩
    exact ⟨w * w', W.mul_mem hw hw', isCoord_mul hwa hwb⟩
  inv_mem' := by
    rintro a ⟨w, hw, hwa⟩
    exact ⟨w⁻¹, W.inv_mem hw, isCoord_inv hwa⟩

theorem mem_ct3_coordSub {W K : Subgroup Y} {j : Y} :
    j ∈ ct3_coordSub W K ↔ ∃ w ∈ W, IsCoord K w j :=
  Iff.rfl

theorem ct3_coord_conj {K : Subgroup Y} {f : Y} (hf : f ∈ K) {w j : Y} (h : IsCoord K w j) :
    IsCoord K (f * w * f⁻¹) (f * j * f⁻¹) :=
  isCoord_mul (isCoord_mul (isCoord_self hf) h) (isCoord_inv (isCoord_self hf))

end Helpers

section Transport

theorem ct3_suzuki_b {X : Type} [Group X] [Finite X] (hK : SuzukiAutFacts) (hXK : CFSG.IsKGroup X)
    {J : Subgroup X}
    (hJc : CFSG.IsComponent J) (hJs : IsSimpleGroup J) (hJ3 : ¬ 3 ∣ Nat.card J) {y : X}
    (hyn : ∀ h : X, h ∈ J ↔ y * h * y⁻¹ ∈ J) (hy3 : y ^ 3 = 1) {N : Subgroup X} (hNJ : N ≤ J)
    (hN2 : IsPGroup 2 N) (hyN : ∀ n ∈ N, y * n = n * y)
    (hcl : ∀ f ∈ J, y * f = f * y → ∀ n ∈ N, f * n * f⁻¹ ∈ N) : N = ⊥ := by
  unfold SuzukiAutFacts at hK
  haveI : Small.{0} X := Small.mk' (Finite.equivFin X)
  let φ : X ≃* Shrink.{0} X := Shrink.mulEquiv.symm
  haveI : Finite (Shrink.{0} X) := Finite.of_equiv X φ.toEquiv
  haveI := hJs
  let eJ : ↥(J.map φ.toMonoidHom) ≃* ↥J := (J.equivMapOfInjective φ.toMonoidHom φ.injective).symm
  have hJ's : IsSimpleGroup ↥(J.map φ.toMonoidHom) := eJ.isSimpleGroup
  have hJ'c : CFSG.IsComponent (J.map φ.toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv φ hJc
  have hJ3' : ¬ 3 ∣ Nat.card ↥(J.map φ.toMonoidHom) := by
    rw [Nat.card_congr eJ.toEquiv]
    exact hJ3
  have hyn' : ∀ h' : Shrink.{0} X, h' ∈ J.map φ.toMonoidHom ↔
      φ y * h' * (φ y)⁻¹ ∈ J.map φ.toMonoidHom := by
    intro h'
    obtain ⟨h, rfl⟩ := φ.surjective h'
    have e1 : φ y * φ h * (φ y)⁻¹ = φ (y * h * y⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e1]
    simp only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact hyn h
  have hyn'' : φ y ∈ Subgroup.normalizer
      ((J.map φ.toMonoidHom : Subgroup (Shrink.{0} X)) : Set (Shrink.{0} X)) :=
    Subgroup.mem_normalizer_iff.mpr fun h' => by simpa only [SetLike.mem_coe] using hyn' h'
  have hy'3 : (φ y) ^ 3 = 1 := by
    rw [← map_pow, hy3, map_one]
  have hcentr : (φ y) ^ 3 ∈ Subgroup.centralizer
      ((J.map φ.toMonoidHom : Subgroup (Shrink.{0} X)) : Set (Shrink.{0} X)) := by
    rw [hy'3]
    exact Subgroup.one_mem _
  have hNJ' : N.map φ.toMonoidHom ≤ J.map φ.toMonoidHom := Subgroup.map_mono hNJ
  have hN2' : IsPGroup 2 ↥(N.map φ.toMonoidHom) :=
    hN2.of_equiv (N.equivMapOfInjective φ.toMonoidHom φ.injective)
  have hyN' : ∀ n ∈ N.map φ.toMonoidHom, φ y * n = n * φ y := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hyN m hm]
  have hcl' : ∀ f ∈ J.map φ.toMonoidHom, φ y * f = f * φ y →
      ∀ n ∈ N.map φ.toMonoidHom, f * n * f⁻¹ ∈ N.map φ.toMonoidHom := by
    intro f hf hfy n hn
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hf
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
    have hgy : y * g = g * y := by
      apply φ.injective
      simpa only [MulEquiv.coe_toMonoidHom, map_mul] using hfy
    have hmem := Subgroup.mem_map_of_mem φ.toMonoidHom (hcl g hg hgy m hm)
    simpa only [MulEquiv.coe_toMonoidHom, map_mul, map_inv] using hmem
  have hb := (hK (Shrink.{0} X) (hXK.of_surjective φ.toMonoidHom φ.surjective) (J.map φ.toMonoidHom)
    hJ's hJ'c.1.1 hJ3' (φ y) hyn'' hcentr).2.1
  have hbot := hb (N.map φ.toMonoidHom) hNJ' hN2' hyN' hcl'
  rw [eq_bot_iff]
  intro m hm
  have h1 : φ.toMonoidHom m ∈ N.map φ.toMonoidHom := Subgroup.mem_map_of_mem φ.toMonoidHom hm
  rw [hbot, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  apply φ.injective
  rw [map_one]
  exact h1

end Transport

variable {X : Type} [Group X] [Finite X]

theorem normal_two_subgroup_of_centralizer_layer_eq_bot (hK : SuzukiAutFacts)
    (hXK : CFSG.IsKGroup X) (hθ : aschbacherSolvableCore 3 X = ⊥)
    (hE : ∀ J : Subgroup X, CFSG.IsComponent J → ¬ 3 ∣ Nat.card J)
    {y : X} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (W : Subgroup X) (hWE : W ≤ CFSG.layer X) (hWC : ∀ w ∈ W, y * w = w * y) (hW2 : IsPGroup 2 W)
    (hWn : ∀ e ∈ CFSG.layer X, y * e = e * y → ∀ w ∈ W, e * w * e⁻¹ ∈ W) : W = ⊥ := by
  have hZ : ∀ J : Subgroup X, CFSG.IsComponent J → Subgroup.center J = ⊥ :=
    fun J hJ => component_center_bot_of_prime_three hθ hJ (hE J hJ)
  have key : ∀ K : Subgroup X, CFSG.IsComponent K → ct3_coordSub W K = ⊥ := by
    intro K hKc
    have hKZ : Subgroup.center K = ⊥ := hZ K hKc
    have hKs : IsSimpleGroup K := isSimpleGroup_of_component_center_bot hKc hKZ
    have hKle : K ≤ CFSG.layer X := CFSG.LocalCores.component_le_layer hKc
    have hpow : ∀ j ∈ ct3_coordSub W K, ∃ n : ℕ, j ^ 2 ^ n = 1 := by
      intro j hj
      obtain ⟨w, hw, hwj⟩ := mem_ct3_coordSub.mp hj
      obtain ⟨n, hn⟩ := hW2 ⟨w, hw⟩
      have hn' : w ^ 2 ^ n = 1 := by
        have := congrArg Subtype.val hn
        simpa using this
      refine ⟨n, ?_⟩
      have h1 : IsCoord K (w ^ 2 ^ n) (j ^ 2 ^ n) := isCoord_pow _ hwj
      rw [hn'] at h1
      exact isCoord_unique hKZ h1 isCoord_one_one
    have hPG : IsPGroup 2 (ct3_coordSub W K) := by
      intro g
      obtain ⟨n, hn⟩ := hpow g.1 g.2
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
    by_cases hyK : K.map (MulAut.conj y).toMonoidHom = K
    ·
      have hyn : ∀ h : X, h ∈ K ↔ y * h * y⁻¹ ∈ K := by
        intro h
        constructor
        · intro hh
          rw [← hyK]
          exact Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hh
        · intro hh
          have hh' : y * h * y⁻¹ ∈ K.map (MulAut.conj y).toMonoidHom := by
            rw [hyK]
            exact hh
          obtain ⟨k, hk, hkh⟩ := Subgroup.mem_map.mp hh'
          have hkh' : y * k * y⁻¹ = y * h * y⁻¹ := hkh
          have hkh'' : k = h := by simpa using hkh'
          rw [← hkh'']
          exact hk
      have hyN : ∀ n ∈ ct3_coordSub W K, y * n = n * y := by
        intro n hn
        obtain ⟨w, hw, hwn⟩ := mem_ct3_coordSub.mp hn
        have h1 : IsCoord K (y * w * y⁻¹) (y * n * y⁻¹) := by
          have := isCoord_conj y hwn
          rw [hyK] at this
          exact this
        rw [hWC w hw, mul_inv_cancel_right] at h1
        have h2 : y * n * y⁻¹ = n := isCoord_unique hKZ h1 hwn
        exact mul_inv_eq_iff_eq_mul.mp h2
      have hcl : ∀ f ∈ K, y * f = f * y → ∀ n ∈ ct3_coordSub W K,
          f * n * f⁻¹ ∈ ct3_coordSub W K := by
        intro f hf hfy n hn
        obtain ⟨w, hw, hwn⟩ := mem_ct3_coordSub.mp hn
        exact mem_ct3_coordSub.mpr ⟨f * w * f⁻¹, hWn f (hKle hf) hfy w hw, ct3_coord_conj hf hwn⟩
      have hNK : ct3_coordSub W K ≤ K := by
        intro j hj
        obtain ⟨w, hw, hwj⟩ := mem_ct3_coordSub.mp hj
        obtain ⟨hjK, -⟩ := hwj
        exact hjK
      exact ct3_suzuki_b hK hXK hKc hKs (hE K hKc) hyn hy3 hNK hPG hyN hcl
    ·
      obtain ⟨K₂, hK₂⟩ : ∃ L : Subgroup X, L = K.map (MulAut.conj y).toMonoidHom := ⟨_, rfl⟩
      obtain ⟨K₃, hK₃⟩ : ∃ L : Subgroup X, L = K.map (MulAut.conj (y ^ 2)).toMonoidHom :=
        ⟨_, rfl⟩
      have hK₂c : CFSG.IsComponent K₂ := by
        rw [hK₂]
        exact CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj y) hKc
      have hK₃c : CFSG.IsComponent K₃ := by
        rw [hK₃]
        exact CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (y ^ 2)) hKc
      obtain ⟨hne3, hne23⟩ := map_conj_sq_ne hy3 hyK
      have hne2 : K₂ ≠ K := by
        rw [hK₂]
        exact hyK
      have hne3' : K₃ ≠ K := by
        rw [hK₃]
        exact hne3
      have hne23' : K₃ ≠ K₂ := by
        rw [hK₃, hK₂]
        exact hne23
      have hc2 : ⁅K, K₂⁆ = ⊥ :=
        (CFSG.LocalCores.distinct_components_commute hKc hK₂c).resolve_left (fun e => hne2 e.symm)
      have hc3 : ⁅K, K₃⁆ = ⊥ :=
        (CFSG.LocalCores.distinct_components_commute hKc hK₃c).resolve_left (fun e => hne3' e.symm)
      have hc23 : ⁅K₂, K₃⁆ = ⊥ :=
        (CFSG.LocalCores.distinct_components_commute hK₂c hK₃c).resolve_left
          (fun e => hne23' e.symm)
      have hc2' : ⁅K₂, K⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact hc2
      have hc3' : ⁅K₃, K⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact hc3
      have hm2 : ∀ k ∈ K, y * k * y⁻¹ ∈ K₂ := fun k hk => by
        rw [hK₂]
        exact Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hk
      have hm3 : ∀ k ∈ K, y ^ 2 * k * (y ^ 2)⁻¹ ∈ K₃ := fun k hk => by
        rw [hK₃]
        exact Subgroup.mem_map_of_mem (MulAut.conj (y ^ 2)).toMonoidHom hk
      have hm2K : ∀ m ∈ K.map (MulAut.conj y).toMonoidHom, m ∈ K₂ := fun m hm => by
        rw [hK₂]
        exact hm
      have hm3K : ∀ m ∈ K.map (MulAut.conj (y ^ 2)).toMonoidHom, m ∈ K₃ := fun m hm => by
        rw [hK₃]
        exact hm
      have hlay2 : ∀ k ∈ K, y * k * y⁻¹ ∈ CFSG.layer X := fun k hk =>
        CFSG.LocalCores.component_le_layer hK₂c (hm2 k hk)
      have hlay3 : ∀ k ∈ K, y ^ 2 * k * (y ^ 2)⁻¹ ∈ CFSG.layer X := fun k hk =>
        CFSG.LocalCores.component_le_layer hK₃c (hm3 k hk)
      have hdiag : ∀ k ∈ K, IsCoord K (diag3 y k) k ∧ y * diag3 y k = diag3 y k * y ∧
          diag3 y k ∈ CFSG.layer X := by
        intro k hk
        refine ⟨?_, ?_, ?_⟩
        · exact isCoord_diag3 hk (fun m hm k' hk' => ct3_comm hc2' (hm2K m hm) hk')
            (fun m hm k' hk' => ct3_comm hc3' (hm3K m hm) hk')
        · exact diag3_comm hy3 (ct3_comm hc2 hk (hm2 k hk)) (ct3_comm hc3 hk (hm3 k hk))
            (ct3_comm hc23 (hm2 k hk) (hm3 k hk))
        · exact mul_mem (mul_mem (hKle hk) (hlay2 k hk)) (hlay3 k hk)
      have hnorm : ∀ k ∈ K, ∀ n ∈ ct3_coordSub W K, k * n * k⁻¹ ∈ ct3_coordSub W K := by
        intro k hk n hn
        obtain ⟨w, hw, hwn⟩ := mem_ct3_coordSub.mp hn
        obtain ⟨hdk, hyd, hdl⟩ := hdiag k hk
        have hdw : diag3 y k * w * (diag3 y k)⁻¹ ∈ W := hWn _ hdl hyd w hw
        exact mem_ct3_coordSub.mpr
          ⟨_, hdw, isCoord_mul (isCoord_mul hdk hwn) (isCoord_inv hdk)⟩
      have hnormal : ((ct3_coordSub W K).subgroupOf K).Normal := by
        refine ⟨fun n hn g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        have := hnorm (g : X) g.2 (n : X) hn
        simpa using this
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((ct3_coordSub W K).subgroupOf K) with
        hbot | htop
      · rw [eq_bot_iff]
        intro j hj
        obtain ⟨w, hw, hwj⟩ := mem_ct3_coordSub.mp hj
        obtain ⟨hjK, -⟩ := hwj
        have hmem : (⟨j, hjK⟩ : K) ∈ (ct3_coordSub W K).subgroupOf K :=
          Subgroup.mem_subgroupOf.mpr hj
        rw [hbot, Subgroup.mem_bot] at hmem
        rw [Subgroup.mem_bot]
        simpa using congrArg Subtype.val hmem
      · exfalso
        have hK2 : IsPGroup 2 K := by
          intro g
          have hg : (g : X) ∈ ct3_coordSub W K := by
            have hgt : g ∈ (ct3_coordSub W K).subgroupOf K := by
              rw [htop]
              exact Subgroup.mem_top g
            exact Subgroup.mem_subgroupOf.mp hgt
          obtain ⟨n, hn⟩ := hpow _ hg
          exact ⟨n, Subtype.ext (by simpa using hn)⟩
        haveI := hK2.isNilpotent
        haveI := hKc.1.1
        exact Group.IsPerfect.not_isSolvable K inferInstance
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  refine eq_one_of_forall_isCoord_one hZ (hWE hw) (fun K hKc => ?_)
  obtain ⟨j, hj⟩ := exists_isCoord_of_mem_layer hKc (hWE hw)
  have hjN : j ∈ ct3_coordSub W K := mem_ct3_coordSub.mpr ⟨w, hw, hj⟩
  rw [key K hKc, Subgroup.mem_bot] at hjN
  rw [hjN] at hj
  exact hj

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

variable {X : Type} [Group X] [Finite X]

theorem ct4_mul_eq_of_bot {G : Type*} [Group G] {A B : Subgroup G} (h : ⁅A, B⁆ = ⊥)
    {a b : G} (ha : a ∈ A) (hb : b ∈ B) : a * b = b * a :=
  (Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha) b hb).symm

theorem ct4_map_map_conj {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [mul_assoc]

theorem ct4_map_conj_one {G : Type*} [Group G] (H : Subgroup G) :
    H.map (MulAut.conj (1 : G)).toMonoidHom = H := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hz
    exact ⟨z, hz, by simp⟩

theorem ct4_suzuki_of_equiv (hK : SuzukiAutFacts) {Y : Type*} {Z : Type} [Group Y] [Group Z]
    [Finite Z] (hZK : CFSG.IsKGroup Z) (e : Y ≃* Z) (J : Subgroup Y) (hJs : IsSimpleGroup J) (hJp : Group.IsPerfect J)
    (h3 : ¬ 3 ∣ Nat.card J) (y : Y) (hyJ : J.map (MulAut.conj y).toMonoidHom = J)
    (hy3 : y ^ 3 = 1) :
    (∃ j ∈ J, j ≠ 1 ∧ y * j = j * y) ∧
    (∀ x : Y, J.map (MulAut.conj x).toMonoidHom = J → x * y = y * x →
      (∃ k : ℕ, x ^ 2 ^ k = 1) → (∀ j ∈ J, y * j = j * y → x * j = j * x) →
      ∀ j ∈ J, x * j = j * x) := by
  have hJ'eq : Nat.card J = Nat.card (J.map e.toMonoidHom) :=
    Nat.card_congr (J.equivMapOfInjective e.toMonoidHom e.injective).toEquiv
  have hJ's : IsSimpleGroup (J.map e.toMonoidHom) :=
    (J.equivMapOfInjective e.toMonoidHom e.injective).isSimpleGroup_congr.mp hJs
  have hJ'p : Group.IsPerfect (J.map e.toMonoidHom) := by
    haveI := hJp
    exact Group.IsPerfect.map e.toMonoidHom
  have h3' : ¬ 3 ∣ Nat.card (J.map e.toMonoidHom) := by
    rw [← hJ'eq]
    exact h3
  have hconj : ∀ g : Y, (J.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom =
      (J.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom := by
    intro g
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext z
    simp
  have hnorm : ∀ g : Y, J.map (MulAut.conj g).toMonoidHom = J →
      e g ∈ Subgroup.normalizer ((J.map e.toMonoidHom : Subgroup Z) : Set Z) := by
    intro g hg
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    exact (hconj g).trans (by rw [hg])
  have hy3' : e y ^ 3 ∈ Subgroup.centralizer ((J.map e.toMonoidHom : Subgroup Z) : Set Z) := by
    rw [← map_pow, hy3, map_one]
    exact one_mem _
  have hF := hK Z hZK (J.map e.toMonoidHom) hJ's hJ'p h3' (e y) (hnorm y hyJ) hy3'
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hzJ, hz1, hzy⟩ := hF.1
    obtain ⟨j, hjJ, hj⟩ := Subgroup.mem_map.mp hzJ
    have hj' : e j = z := hj
    refine ⟨j, hjJ, ?_, ?_⟩
    · intro h
      apply hz1
      rw [← hj', h, map_one]
    · apply e.injective
      rw [map_mul, map_mul, hj']
      exact hzy
  · intro x hxJ hxy hx2 hC j hjJ
    have hxy' : e x * e y = e y * e x := by
      rw [← map_mul, ← map_mul, hxy]
    have hx2' : ∃ k : ℕ, e x ^ 2 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hx2
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    have hC' : ∀ j' ∈ J.map e.toMonoidHom, e y * j' = j' * e y → e x * j' = j' * e x := by
      intro j' hj' hjy
      obtain ⟨j0, hj0, hj0e⟩ := Subgroup.mem_map.mp hj'
      have hj0e' : e j0 = j' := hj0e
      subst hj0e'
      have hyj : y * j0 = j0 * y := by
        apply e.injective
        rw [map_mul, map_mul]
        exact hjy
      rw [← map_mul, ← map_mul, hC j0 hj0 hyj]
    have hres := hF.2.2 (e x) (hnorm x hxJ) hxy' hx2' hC' (e j)
      (Subgroup.mem_map_of_mem e.toMonoidHom hjJ)
    apply e.injective
    rw [map_mul, map_mul]
    exact hres

theorem ct4_suzuki_univ (hK : SuzukiAutFacts) {Y : Type} [Group Y] [Finite Y] (hYK : CFSG.IsKGroup Y)
    (J : Subgroup Y)
    (hJs : IsSimpleGroup J) (hJp : Group.IsPerfect J) (h3 : ¬ 3 ∣ Nat.card J) (y : Y)
    (hyJ : J.map (MulAut.conj y).toMonoidHom = J) (hy3 : y ^ 3 = 1) :
    (∃ j ∈ J, j ≠ 1 ∧ y * j = j * y) ∧
    (∀ x : Y, J.map (MulAut.conj x).toMonoidHom = J → x * y = y * x →
      (∃ k : ℕ, x ^ 2 ^ k = 1) → (∀ j ∈ J, y * j = j * y → x * j = j * x) →
      ∀ j ∈ J, x * j = j * x) := by
  let e : Y ≃* (Shrink Y : Type) := Shrink.mulEquiv.symm
  haveI : Finite (Shrink Y : Type) := Finite.of_equiv Y e.toEquiv
  exact ct4_suzuki_of_equiv hK (hYK.of_surjective e.toMonoidHom e.surjective) e J hJs hJp h3 y hyJ hy3

theorem two_element_centralizes_layer (hK : SuzukiAutFacts) (hXK : CFSG.IsKGroup X)
    (hθ : aschbacherSolvableCore 3 X = ⊥)
    (hE : ∀ J : Subgroup X, CFSG.IsComponent J → ¬ 3 ∣ Nat.card J)
    {y : X} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    {x : X} (hxy : x * y = y * x) (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hxC : ∀ e ∈ CFSG.layer X, y * e = e * y → x * e = e * x) :
    ∀ e ∈ CFSG.layer X, x * e = e * x := by
  have hZ : ∀ J : Subgroup X, CFSG.IsComponent J → Subgroup.center J = ⊥ :=
    fun J hJ => component_center_bot_of_prime_three hθ hJ (hE J hJ)
  have hmain : ∀ K : Subgroup X, CFSG.IsComponent K → ∀ k ∈ K, x * k = k * x := by
    intro K hKc
    have hZK : Subgroup.center K = ⊥ := hZ K hKc
    have hKs : IsSimpleGroup K := isSimpleGroup_of_component_center_bot hKc hZK
    have hKp : Group.IsPerfect K := hKc.1.1
    have hK3 : ¬ 3 ∣ Nat.card K := hE K hKc
    have hKL : ∀ k ∈ K, k ∈ CFSG.layer X := fun k hk =>
      CFSG.LocalCores.component_le_layer hKc hk
    by_cases hA : K.map (MulAut.conj y).toMonoidHom = K
    ·
      obtain ⟨e1, he1K, he1, hye⟩ := (ct4_suzuki_univ hK hXK K hKs hKp hK3 y hA hy3).1
      have hxe1 : x * e1 = e1 * x := hxC e1 (hKL e1 he1K) hye
      have hmemx : e1 ∈ K.map (MulAut.conj x).toMonoidHom :=
        ⟨e1, he1K, by
          show x * e1 * x⁻¹ = e1
          rw [hxe1, mul_inv_cancel_right]⟩
      have hKxK : K.map (MulAut.conj x).toMonoidHom = K := by
        by_contra hne
        have hinf := compJ3_inf_eq_bot hKc
          (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hKc) (Ne.symm hne) hZK
        have he1mem : e1 ∈ K ⊓ K.map (MulAut.conj x).toMonoidHom :=
          Subgroup.mem_inf.mpr ⟨he1K, hmemx⟩
        rw [hinf, Subgroup.mem_bot] at he1mem
        exact he1 he1mem
      exact (ct4_suzuki_univ hK hXK K hKs hKp hK3 y hA hy3).2 x hKxK hxy hx2
        (fun j hj hjy => hxC j (hKL j hj) hjy)
    ·
      have hA' : K.map (MulAut.conj y).toMonoidHom ≠ K := hA
      obtain ⟨hK3K, hK3K2⟩ := map_conj_sq_ne hy3 hA'
      set K₂ : Subgroup X := K.map (MulAut.conj y).toMonoidHom with hK₂def
      set K₃ : Subgroup X := K.map (MulAut.conj (y ^ 2)).toMonoidHom with hK₃def
      have hK2c : CFSG.IsComponent K₂ :=
        CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj y) hKc
      have hK3c : CFSG.IsComponent K₃ :=
        CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (y ^ 2)) hKc
      have hbot2 : ⁅K, K₂⁆ = ⊥ :=
        (CFSG.LocalCores.distinct_components_commute hKc hK2c).resolve_left (Ne.symm hA')
      have hbot3 : ⁅K, K₃⁆ = ⊥ :=
        (CFSG.LocalCores.distinct_components_commute hKc hK3c).resolve_left (Ne.symm hK3K)
      have hbot23 : ⁅K₂, K₃⁆ = ⊥ :=
        (CFSG.LocalCores.distinct_components_commute hK2c hK3c).resolve_left (Ne.symm hK3K2)
      have hmem2 : ∀ k ∈ K, y * k * y⁻¹ ∈ K₂ := fun k hk => ⟨k, hk, rfl⟩
      have hmem3 : ∀ k ∈ K, y ^ 2 * k * (y ^ 2)⁻¹ ∈ K₃ := fun k hk => ⟨k, hk, rfl⟩
      have hdiag : ∀ k ∈ K, y * diag3 y k = diag3 y k * y := fun k hk =>
        diag3_comm hy3 (ct4_mul_eq_of_bot hbot2 hk (hmem2 k hk))
          (ct4_mul_eq_of_bot hbot3 hk (hmem3 k hk))
          (ct4_mul_eq_of_bot hbot23 (hmem2 k hk) (hmem3 k hk))
      have hdK : ∀ k ∈ K, IsCoord K (diag3 y k) k := fun k hk =>
        isCoord_diag3 hk (fun m hm k' hk' => (ct4_mul_eq_of_bot hbot2 hk' hm).symm)
          (fun m hm k' hk' => (ct4_mul_eq_of_bot hbot3 hk' hm).symm)
      have hdL : ∀ k ∈ K, diag3 y k ∈ CFSG.layer X := fun k hk => by
        unfold diag3
        exact (CFSG.layer X).mul_mem
          ((CFSG.layer X).mul_mem (hKL k hk)
            (CFSG.LocalCores.component_le_layer hK2c (hmem2 k hk)))
          (CFSG.LocalCores.component_le_layer hK3c (hmem3 k hk))
      have hxd : ∀ k ∈ K, x * diag3 y k = diag3 y k * x := fun k hk =>
        hxC _ (hdL k hk) (hdiag k hk)
      have hxconj : ∀ k ∈ K, x * diag3 y k * x⁻¹ = diag3 y k := fun k hk => by
        rw [hxd k hk, mul_inv_cancel_right]
      have hdconj : ∀ k : X, diag3 y (x * k * x⁻¹) = x * diag3 y k * x⁻¹ := fun k =>
        (conj_diag3 (k := k) hxy).symm
      have hKxK : K.map (MulAut.conj x).toMonoidHom = K := by
        have hmem : K.map (MulAut.conj x).toMonoidHom = K ∨
            K.map (MulAut.conj x).toMonoidHom = K₂ ∨
            K.map (MulAut.conj x).toMonoidHom = K₃ := by
          by_contra hcon
          simp only [not_or] at hcon
          obtain ⟨hn1, hn2, hn3⟩ := hcon
          obtain ⟨k, hk, hk1⟩ : ∃ k ∈ K, k ≠ 1 := by
            obtain ⟨⟨k, hk⟩, hne⟩ := exists_ne (1 : K)
            exact ⟨k, hk, fun h => hne (Subtype.ext h)⟩
          set K' : Subgroup X := K.map (MulAut.conj x).toMonoidHom with hK'def
          have hK'c : CFSG.IsComponent K' :=
            CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hKc
          have hK'y_ne : K'.map (MulAut.conj y).toMonoidHom ≠ K := by
            intro h
            apply hn3
            have hy21 : y ^ 2 * y = 1 := by
              rw [← pow_succ]
              exact hy3
            have h' : K₃ = K' := by
              rw [hK₃def, ← h, ct4_map_map_conj, hy21, ct4_map_conj_one]
            exact h'.symm
          have hK'y2_ne : K'.map (MulAut.conj (y ^ 2)).toMonoidHom ≠ K := by
            intro h
            apply hn2
            have hy12 : y * y ^ 2 = 1 := by
              rw [← pow_succ']
              exact hy3
            have h' : K₂ = K' := by
              rw [hK₂def, ← h, ct4_map_map_conj, hy12, ct4_map_conj_one]
            exact h'.symm
          have hbotK' : ⁅K, K'⁆ = ⊥ :=
            (CFSG.LocalCores.distinct_components_commute hKc hK'c).resolve_left (Ne.symm hn1)
          have hbotK'y : ⁅K, K'.map (MulAut.conj y).toMonoidHom⁆ = ⊥ :=
            (CFSG.LocalCores.distinct_components_commute hKc
              (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj y) hK'c)).resolve_left
              (Ne.symm hK'y_ne)
          have hbotK'y2 : ⁅K, K'.map (MulAut.conj (y ^ 2)).toMonoidHom⁆ = ⊥ :=
            (CFSG.LocalCores.distinct_components_commute hKc
              (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (y ^ 2)) hK'c)).resolve_left
              (Ne.symm hK'y2_ne)
          have hkx : x * k * x⁻¹ ∈ K' := ⟨k, hk, rfl⟩
          have hm2 : y * (x * k * x⁻¹) * y⁻¹ ∈ K'.map (MulAut.conj y).toMonoidHom :=
            ⟨x * k * x⁻¹, hkx, rfl⟩
          have hm3 : y ^ 2 * (x * k * x⁻¹) * (y ^ 2)⁻¹ ∈
              K'.map (MulAut.conj (y ^ 2)).toMonoidHom :=
            ⟨x * k * x⁻¹, hkx, rfl⟩
          have hcentral : ∀ k' ∈ K, diag3 y (x * k * x⁻¹) * k' = k' * diag3 y (x * k * x⁻¹) := by
            intro k' hk'
            have c1 : Commute (x * k * x⁻¹) k' := (ct4_mul_eq_of_bot hbotK' hk' hkx).symm
            have c2 : Commute (y * (x * k * x⁻¹) * y⁻¹) k' :=
              (ct4_mul_eq_of_bot hbotK'y hk' hm2).symm
            have c3 : Commute (y ^ 2 * (x * k * x⁻¹) * (y ^ 2)⁻¹) k' :=
              (ct4_mul_eq_of_bot hbotK'y2 hk' hm3).symm
            unfold diag3
            exact ((c1.mul_left c2).mul_left c3).eq
          have hone : IsCoord K (diag3 y (x * k * x⁻¹)) 1 :=
            isCoord_one_of_centralizes hcentral
          have hdeq : diag3 y (x * k * x⁻¹) = diag3 y k := (hdconj k).trans (hxconj k hk)
          rw [hdeq] at hone
          exact hk1 (isCoord_unique (hZ K hKc) (hdK k hk) hone)
        exact conj_eq_of_orbit hy3 hxy hx2 hA' hmem
      intro k hk
      have h1 := isCoord_conj x (hdK k hk)
      rw [hKxK, hxconj k hk] at h1
      have h2 := isCoord_unique (hZ K hKc) (hdK k hk) h1
      exact mul_inv_eq_iff_eq_mul.mp h2.symm
  have hsub : CFSG.layer X ≤ Subgroup.centralizer ({x} : Set X) := by
    rw [CFSG.layer.eq_sSup X]
    refine sSup_le fun K hKc => ?_
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact hmain K hKc k hk
  intro e he
  exact Subgroup.mem_centralizer_iff.mp (hsub he) x (Set.mem_singleton x)

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

@[expose] def ThreePrimeComponentsTwoCore : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsKGroup X → aschbacherSolvableCore 3 X = ⊥ →
    (∀ J : Subgroup X, CFSG.IsComponent J → ¬ 3 ∣ Nat.card J) →
      ∀ y : X, orderOf y = 3 →
        inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set X)) = ⊥

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem threePrimeComponentsTwoCore_of (hK : SuzukiAutFacts) : ThreePrimeComponentsTwoCore := by
  intro X _ _ hXK hθ hE y hy
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy
    norm_num at hy
  set Z := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set X)) with hZdef
  have hZC : Z ≤ Subgroup.centralizer ({y} : Set X) := Subgroup.map_subtype_le _
  have hZ2 : IsPGroup 2 Z := by
    rw [hZdef]
    unfold inSubgroup
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥(Subgroup.centralizer ({y} : Set X)))).map _
  have hZnorm : Subgroup.centralizer ({y} : Set X) ≤ Subgroup.normalizer (Z : Set X) :=
    compJ1_le_normalizer_inSubgroup_pCore 2 _
  have hZ3 : Z ≤ Subgroup.centralizer ((CFSG.pCore 3 X : Subgroup X) : Set X) :=
    pCore_two_centralizer_le_centralizer_pCore_three hy3
  have hcomm : ∀ x ∈ Z, x * y = y * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hZC hx)
  haveI hLchar : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic (G := X)
  have hLn : (CFSG.layer X).Normal := inferInstance
  rw [eq_bot_iff]
  intro x hx
  have hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hZ2 ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hW : Z ⊓ CFSG.layer X = ⊥ := by
    refine normal_two_subgroup_of_centralizer_layer_eq_bot hK hXK hθ hE hy3 hy1 _ inf_le_right
      (fun w hw => (hcomm w (Subgroup.mem_inf.mp hw).1).symm)
      (hZ2.to_le inf_le_left) ?_
    intro e he hye w hw
    have hwZ : w ∈ Z := (Subgroup.mem_inf.mp hw).1
    have hwE : w ∈ CFSG.layer X := (Subgroup.mem_inf.mp hw).2
    have heC : e ∈ Subgroup.centralizer ({y} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hye.symm
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hZnorm heC) w).mp hwZ
    · exact hLn.conj_mem w hwE e
  have hxC : ∀ e ∈ CFSG.layer X, y * e = e * y → x * e = e * x := by
    intro e he hye
    have heC : e ∈ Subgroup.centralizer ({y} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hye.symm
    have h1 : x * e * x⁻¹ * e⁻¹ ∈ Z ⊓ CFSG.layer X := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have hz : e * x⁻¹ * e⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hZnorm heC) x⁻¹).mp
          (inv_mem hx)
        have : x * e * x⁻¹ * e⁻¹ = x * (e * x⁻¹ * e⁻¹) := by group
        rw [this]
        exact mul_mem hx hz
      · have h2 : x * e * x⁻¹ ∈ CFSG.layer X := hLn.conj_mem e he x
        exact mul_mem h2 (inv_mem he)
    rw [hW, Subgroup.mem_bot] at h1
    calc x * e = (x * e * x⁻¹ * e⁻¹) * (e * x) := by group
      _ = e * x := by rw [h1, one_mul]
  have hL := two_element_centralizes_layer hK hXK hθ hE hy3 hy1 (hcomm x hx) hx2 hxC
  have hO : ∀ o ∈ CFSG.pCore 3 X, x * o = o * x := fun o ho =>
    (Subgroup.mem_centralizer_iff.mp (hZ3 hx) o ho).symm
  exact Subgroup.mem_bot.mpr (eq_one_of_centralizes_layer_pCore_three hθ hx2 hL hO)

end CFSG.RankThree.PartTwo.Sec11
