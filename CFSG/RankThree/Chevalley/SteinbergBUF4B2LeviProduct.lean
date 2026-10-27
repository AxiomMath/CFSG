module

public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardQuasisimple
public import CFSG.RankThree.Chevalley.SteinbergBNF4PairSL3

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley SteinbergBN

theorem exists_prod_mulEquiv_of_commute {G : Type*} [Group G] {A B C : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hdisj : A ⊓ B = ⊥) (hsup : A ⊔ B = C) :
    ∃ e : A × B ≃* C, ∀ p : A × B, (e p : G) = p.1 * p.2 := by
  let φ : A × B →* G := A.subtype.noncommCoprod B.subtype fun a b => hcomm a a.2 b b.2
  have hφ : ∀ p, φ p = p.1 * p.2 := fun p => rfl
  have hrange : φ.range = C := by
    rw [← hsup]
    refine le_antisymm ?_ (sup_le (fun a ha => ⟨(⟨a, ha⟩, 1), by rw [hφ]; simp⟩)
      fun b hb => ⟨(1, ⟨b, hb⟩), by rw [hφ]; simp⟩)
    rintro _ ⟨p, rfl⟩
    rw [hφ]
    exact mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ h
    rw [hφ] at h
    have hab : (a : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hmem : (a : G) ∈ A ⊓ B := Subgroup.mem_inf.2 ⟨a.2, by rw [hab]; exact inv_mem b.2⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    have hb : (b : G) = 1 := by
      rw [hmem, eq_comm, inv_eq_one] at hab
      exact hab
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hb)
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun p => rfl⟩

variable {M : Type} [Field M]

theorem commute_xUnit_yUnit_of_torusRootChar
    {z : ModGL Tag.F4 M} (hz : z ∈ torusGroup Tag.F4 M)
    {k : Fin Tag.F4.rank} (hk : torusRootChar z (Pi.single k 1) = 1) (c : M) :
    z * xUnit Tag.F4 M k c = xUnit Tag.F4 M k c * z ∧
      z * yUnit Tag.F4 M k c = yUnit Tag.F4 M k c * z := by
  have ha : (z : Module.End M (RootModule Tag.F4 M)) (rootVec Tag.F4 M (Pi.single k 1)) =
      (1 : M) • rootVec Tag.F4 M (Pi.single k 1) := by
    rw [apply_rootVec_of_mem_torusGroup hz (isRoot_single _ k), hk]
  obtain ⟨-, hx, hy⟩ := conj_xUnit_of_apply_single hz ha
  constructor
  · calc z * xUnit Tag.F4 M k c = z * xUnit Tag.F4 M k c * z⁻¹ * z := by group
      _ = xUnit Tag.F4 M k c * z := by rw [hx, one_mul]
  · calc z * yUnit Tag.F4 M k c = z * yUnit Tag.F4 M k c * z⁻¹ * z := by group
      _ = yUnit Tag.F4 M k c * z := by rw [hy, inv_one, one_mul]

theorem commute_of_mem_subsystemGroup
    {z : ModGL Tag.F4 M} (hz : z ∈ torusGroup Tag.F4 M)
    {J : Set (Fin Tag.F4.rank)} (hJ : ∀ k ∈ J, torusRootChar z (Pi.single k 1) = 1)
    {x : ModGL Tag.F4 M} (hx : x ∈ subsystemGroup Tag.F4 M J) : z * x = x * z := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, c, rfl | rfl⟩ := hx
    · exact (commute_xUnit_yUnit_of_torusRootChar hz (hJ k hk) c).1
    · exact (commute_xUnit_yUnit_of_torusRootChar hz (hJ k hk) c).2
  | one => rw [mul_one, one_mul]
  | mul x y _ _ hx hy => rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
  | inv x _ hx =>
    calc z * x⁻¹ = x⁻¹ * (x * z) * x⁻¹ := by group
      _ = x⁻¹ * (z * x) * x⁻¹ := by rw [hx]
      _ = x⁻¹ * z := by group

theorem torusRootChar_eq_one_of_commute
    {z : ModGL Tag.F4 M} (hz : z ∈ torusGroup Tag.F4 M)
    {k : Fin Tag.F4.rank} (hc : ∀ c : M, z * xUnit Tag.F4 M k c = xUnit Tag.F4 M k c * z) :
    torusRootChar z (Pi.single k 1) = 1 :=
  (commute_pinnedX_iff hz (isRoot_single _ k)).1 fun c => by rw [pinnedX_single]; exact hc c

theorem f4_cartan_pairing :
    (∑ j, Tag.F4.cartan 1 j * (Pi.single 1 1 : Fin Tag.F4.rank → ℤ) j) = 2 ∧
    (∑ j, Tag.F4.cartan 2 j * (Pi.single 1 1 : Fin Tag.F4.rank → ℤ) j) = -2 ∧
    (∑ j, Tag.F4.cartan 1 j * (Pi.single 2 1 : Fin Tag.F4.rank → ℤ) j) = -1 ∧
    (∑ j, Tag.F4.cartan 2 j * (Pi.single 2 1 : Fin Tag.F4.rank → ℤ) j) = 2 := by
  decide +kernel

theorem torusElt_mem_diagonalGroup
    (i : Fin Tag.F4.rank) (t : Mˣ) :
    torusElt Tag.F4 M i t ∈ diagonalGroup :=
  torusGroup_le_diagonalGroup (Subgroup.subset_closure ⟨(i, t), rfl⟩)

theorem torusRootChar_torus_pair
    (t u : Mˣ) :
    torusRootChar (torusElt Tag.F4 M 1 t * torusElt Tag.F4 M 2 u) (Pi.single 1 1) =
        (t : M) ^ 2 * ((u : M) ^ 2)⁻¹ ∧
      torusRootChar (torusElt Tag.F4 M 1 t * torusElt Tag.F4 M 2 u) (Pi.single 2 1) =
        (t : M)⁻¹ * (u : M) ^ 2 := by
  obtain ⟨e11, e21, e12, e22⟩ := f4_cartan_pairing
  rw [torusRootChar_mul (torusElt_mem_diagonalGroup 1 t) (torusElt_mem_diagonalGroup 2 u),
    torusRootChar_mul (torusElt_mem_diagonalGroup 1 t) (torusElt_mem_diagonalGroup 2 u),
    torusRootChar_torusElt _ _ (isRoot_single _ 1), torusRootChar_torusElt _ _ (isRoot_single _ 1),
    torusRootChar_torusElt _ _ (isRoot_single _ 2), torusRootChar_torusElt _ _ (isRoot_single _ 2),
    e11, e21, e12, e22]
  simp only [Units.val_zpow_eq_zpow_val]
  constructor
  · rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast,
      show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
  · rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast, pow_one,
      show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]

theorem exists_torus_pair_torusRootChar
    [Finite M] [CharP M 2] {h : ModGL Tag.F4 M}
    (hh : h ∈ torusGroup Tag.F4 M) : ∃ t u : Mˣ,
      torusRootChar (torusElt Tag.F4 M 1 t * torusElt Tag.F4 M 2 u) (Pi.single 1 1) =
          torusRootChar h (Pi.single 1 1) ∧
        torusRootChar (torusElt Tag.F4 M 1 t * torusElt Tag.F4 M 2 u) (Pi.single 2 1) =
          torusRootChar h (Pi.single 2 1) := by
  have := Fintype.ofFinite M
  set b := torusRootChar h (Pi.single 1 1)
  set c := torusRootChar h (Pi.single 2 1)
  have hb : b ≠ 0 := torusRootChar_ne_zero (torusGroup_le_diagonalGroup hh) _
  have hc : c ≠ 0 := torusRootChar_ne_zero (torusGroup_le_diagonalGroup hh) _
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq M 2) b
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact hb hs
  refine ⟨Units.mk0 (b * c) (mul_ne_zero hb hc), Units.mk0 (c * s) (mul_ne_zero hc hs0), ?_⟩
  obtain ⟨e1, e2⟩ := torusRootChar_torus_pair (M := M) (Units.mk0 (b * c) (mul_ne_zero hb hc))
    (Units.mk0 (c * s) (mul_ne_zero hc hs0))
  rw [e1, e2, Units.val_mk0, Units.val_mk0]
  constructor
  · field_simp
    rw [hs]
    ring
  · field_simp
    rw [hs]
    ring

section Levi

theorem val_image_f4B2Pair : Fin.val '' ({1, 2} : Set (Fin Tag.F4.rank)) = ({1, 2} : Set ℕ) := by
  rw [Set.image_insert_eq, Set.image_singleton]
  rfl

theorem center_subsystemGroup_f4B2Pair
    [CharP M 2] :
    Subgroup.center (subsystemGroup Tag.F4 M {1, 2}) = ⊥ :=
  center_subsystemGroup_F4_eq_bot (Or.inl val_image_f4B2Pair)

variable {Z L : Subgroup (ModGL Tag.F4 M)}
  (hZ : ∀ h, h ∈ Z ↔ h ∈ torusGroup Tag.F4 M ∧ torusRootChar h (Pi.single 1 1) = 1 ∧
    torusRootChar h (Pi.single 2 1) = 1)
include hZ

theorem le_torusGroup_of_char
    : Z ≤ torusGroup Tag.F4 M := fun h hh => ((hZ h).1 hh).1

theorem commute_of_mem_char
    {z x : ModGL Tag.F4 M} (hz : z ∈ Z)
    (hx : x ∈ subsystemGroup Tag.F4 M {1, 2}) : z * x = x * z := by
  obtain ⟨hzH, h1, h2⟩ := (hZ z).1 hz
  refine commute_of_mem_subsystemGroup hzH (fun k hk => ?_) hx
  rcases hk with rfl | rfl
  · exact h1
  · exact h2

variable [CharP M 2]

theorem char_inf_subsystemGroup
    : Z ⊓ subsystemGroup Tag.F4 M {1, 2} = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz, hzQ⟩
  have hc : (⟨z, hzQ⟩ : subsystemGroup Tag.F4 M {1, 2}) ∈
      Subgroup.center (subsystemGroup Tag.F4 M {1, 2}) := by
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (commute_of_mem_char hZ hz x.2).symm
  rw [center_subsystemGroup_f4B2Pair, Subgroup.mem_bot] at hc
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hc)

theorem eq_of_char_mul_eq
    {z z' x x' : ModGL Tag.F4 M} (hz : z ∈ Z) (hz' : z' ∈ Z)
    (hx : x ∈ subsystemGroup Tag.F4 M {1, 2}) (hx' : x' ∈ subsystemGroup Tag.F4 M {1, 2})
    (h : z * x = z' * x') : z = z' ∧ x = x' := by
  have hm : z'⁻¹ * z = x' * x⁻¹ := by
    calc z'⁻¹ * z = z'⁻¹ * (z * x) * x⁻¹ := by group
      _ = x' * x⁻¹ := by rw [h]; group
  have hmem : z'⁻¹ * z ∈ Z ⊓ subsystemGroup Tag.F4 M {1, 2} :=
    Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hz') hz, by rw [hm]; exact mul_mem hx' (inv_mem hx)⟩
  rw [char_inf_subsystemGroup hZ, Subgroup.mem_bot] at hmem
  have h1 : z = z' := by
    rw [← mul_left_cancel_iff (a := z'⁻¹), hmem, inv_mul_cancel]
  refine ⟨h1, ?_⟩
  rw [h1] at h
  exact mul_left_cancel h

variable [Finite M]

theorem torusGroup_le_char_sup
    : torusGroup Tag.F4 M ≤ Z ⊔ subsystemGroup Tag.F4 M {1, 2} := by
  intro h hh
  obtain ⟨t, u, e1, e2⟩ := exists_torus_pair_torusRootChar hh
  set T := torusElt Tag.F4 M 1 t * torusElt Tag.F4 M 2 u with hT
  have hTH : T ∈ torusGroup Tag.F4 M := mul_mem (Subgroup.subset_closure ⟨(1, t), rfl⟩)
    (Subgroup.subset_closure ⟨(2, u), rfl⟩)
  have hTQ : T ∈ subsystemGroup Tag.F4 M {1, 2} := torusElt_pair_mem 1 2 t u
  have hD := torusGroup_le_diagonalGroup hh
  have hDT := torusGroup_le_diagonalGroup hTH
  have hz : h * T⁻¹ ∈ Z := by
    refine (hZ _).2 ⟨mul_mem hh (inv_mem hTH), ?_, ?_⟩
    · rw [torusRootChar_mul hD (inv_mem hDT), torusRootChar_inv hDT, e1,
        mul_inv_cancel₀ (torusRootChar_ne_zero hD _)]
    · rw [torusRootChar_mul hD (inv_mem hDT), torusRootChar_inv hDT, e2,
        mul_inv_cancel₀ (torusRootChar_ne_zero hD _)]
  have e : h = h * T⁻¹ * T := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right hTQ)

variable (hL : L = torusGroup Tag.F4 M ⊔ subsystemGroup Tag.F4 M {1, 2})
include hL

theorem char_sup_subsystemGroup
    : Z ⊔ subsystemGroup Tag.F4 M {1, 2} = L := by
  rw [hL]
  refine le_antisymm (sup_le_sup_right (le_torusGroup_of_char hZ) _)
    (sup_le (torusGroup_le_char_sup hZ) le_sup_right)

theorem exists_levi_prod_mulEquiv :
    ∃ e : Z × subsystemGroup Tag.F4 M {1, 2} ≃* L,
      ∀ p, (e p : ModGL Tag.F4 M) = p.1 * p.2 :=
  exists_prod_mulEquiv_of_commute (fun _ hz _ hx => commute_of_mem_char hZ hz hx)
    (char_inf_subsystemGroup hZ) (char_sup_subsystemGroup hZ hL)

theorem exists_char_mul_of_mem_levi
    {g : ModGL Tag.F4 M} (hg : g ∈ L) :
    ∃ z ∈ Z, ∃ x ∈ subsystemGroup Tag.F4 M {1, 2}, g = z * x := by
  obtain ⟨e, he⟩ := exists_levi_prod_mulEquiv hZ hL
  refine ⟨_, (e.symm ⟨g, hg⟩).1.2, _, (e.symm ⟨g, hg⟩).2.2, ?_⟩
  rw [← he, MulEquiv.apply_symm_apply]

theorem map_center_levi
    : (Subgroup.center L).map L.subtype = Z := by
  have hZL : Z ≤ L := (char_sup_subsystemGroup hZ hL) ▸ le_sup_left
  have hQL : subsystemGroup Tag.F4 M {1, 2} ≤ L := (char_sup_subsystemGroup hZ hL) ▸ le_sup_right
  have hHcomm := (triangular_borel_structure.{0, 0} Tag.F4 M).1
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨z, hz, x, hx, hgzx⟩ := exists_char_mul_of_mem_levi hZ hL g.2
    have hxc : (⟨x, hx⟩ : subsystemGroup Tag.F4 M {1, 2}) ∈
        Subgroup.center (subsystemGroup Tag.F4 M {1, 2}) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hgy := congrArg Subtype.val ((Subgroup.mem_center_iff.1 hg) ⟨y, hQL y.2⟩)
      simp only [Subgroup.coe_mul] at hgy
      rw [hgzx] at hgy
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      have hzy := commute_of_mem_char hZ hz y.2
      calc (y : ModGL Tag.F4 M) * x = z⁻¹ * (y * (z * x)) := by
            rw [← mul_assoc (y : ModGL Tag.F4 M) z x, ← hzy]; group
        _ = z⁻¹ * (z * x * y) := by rw [hgy]
        _ = x * y := by group
    rw [center_subsystemGroup_f4B2Pair, Subgroup.mem_bot] at hxc
    have hx1 : x = 1 := congrArg Subtype.val hxc
    rw [Subgroup.coe_subtype, hgzx, hx1, mul_one]
    exact hz
  · intro z hz
    refine Subgroup.mem_map.2 ⟨⟨z, hZL hz⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
    obtain ⟨z', hz', x, hx, hg⟩ := exists_char_mul_of_mem_levi hZ hL g.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hg]
    have h1 : z' * z = z * z' := hHcomm z' (le_torusGroup_of_char hZ hz') z
      (le_torusGroup_of_char hZ hz)
    have h2 : z * x = x * z := commute_of_mem_char hZ hz hx
    calc z' * x * z = z' * (x * z) := mul_assoc _ _ _
      _ = z * (z' * x) := by rw [← h2, ← mul_assoc, h1, mul_assoc]

omit hL in
theorem odd_card_char
    : Odd (Nat.card Z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := Tag.F4) (K := M)
  have hdvd : Nat.card Z ∣ Nat.card (torusGroup Tag.F4 M) :=
    Subgroup.card_dvd_of_le (le_torusGroup_of_char hZ)
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  exact fun h2 => not_dvd_card_torusGroup (τ := Tag.F4) (K := M) 2 (h2.trans hdvd)

end Levi

end CFSG.RankThree.Chevalley
