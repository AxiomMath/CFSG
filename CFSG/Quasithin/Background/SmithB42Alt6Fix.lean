module

public import CFSG.Quasithin.Background.SmithB42Alt6Norm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6D8

public section

namespace CFSG.Quasithin

namespace B42Alt6

open CFSG.Open CFSG.QuasithinUnique Equiv Equiv.Perm CFSG.Quasithin.S143

variable {S : Type} [CommGroup S] {G L : Subgroup (MulAut S)}

theorem fix_closure_iff (T : Set (Perm (Fin 6))) (a : N6) :
    (∀ σ ∈ Subgroup.closure T, n6Act σ a = a) ↔ ∀ σ ∈ T, n6Act σ a = a := by
  constructor
  · exact fun h σ hσ => h σ (Subgroup.subset_closure hσ)
  · intro h σ hσ
    let St : Subgroup (Perm (Fin 6)) :=
      { carrier := {σ | n6Act σ a = a}
        one_mem' := by simp
        mul_mem' := fun {x y} hx hy => by
          show n6Act (x * y) a = a
          rw [map_mul, MulAut.mul_apply, show n6Act y a = a from hy, show n6Act x a = a from hx]
        inv_mem' := fun {x} hx => by
          show n6Act x⁻¹ a = a
          have hx' : n6Act x a = a := hx
          rw [map_inv]
          conv_lhs => rw [← hx']
          simp }
    have hle : Subgroup.closure T ≤ St := (Subgroup.closure_le St).2 h
    exact hle hσ

theorem N6Model.card_fixV_closure (M : N6Model L) (T : Set (Perm (Fin 6))) :
    Nat.card (fixV ((Subgroup.closure T).map M.ρ)) =
      Nat.card {a : N6 // ∀ σ ∈ T, n6Act σ a = a} := by
  rw [M.card_fixV_map]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun a => fix_closure_iff T a)

theorem card_fix_swap :
    (Finset.univ.filter fun a : N6 => n6Act (swap 0 1) a = a).card = 8 := by decide +kernel

theorem card_fix_V0 :
    (Finset.univ.filter fun a : N6 =>
      n6Act (swap 0 1 * swap 2 3) a = a ∧ n6Act (swap 0 2 * swap 1 3) a = a).card = 2 := by
  decide +kernel

theorem N6Model.card_fixV_swap (M : N6Model L) :
    Nat.card (fixV (Subgroup.zpowers (M.ρ (swap 0 1)))) = 8 := by
  rw [← MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure, M.card_fixV_closure,
    ← card_fix_swap, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun a => by simp)

theorem exists_rank [Finite S] (C : Ctx G L) (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤)
    (hcard : Nat.card S = 16) {B : Subgroup (MulAut S)} (hBG : B ≤ G) (hB1 : B ≠ ⊥)
    (hB : IsElemAbelian2 B) :
    ∃ r i : ℕ, Nat.card B = 2 ^ r ∧ (fixV B).index = 2 ^ i ∧ 1 ≤ r ∧ r ≤ 3 ∧ 2 * r ≤ 3 * i := by
  obtain ⟨r, m, hr, hr1, hr3, hmr, hle⟩ := card_le_index_pow C hirr hBG hB1 hB
  have hdvd : (fixV B).index ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← hcard]
    exact Subgroup.index_dvd_card _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  refine ⟨r, i, hr, hi, hr1, hr3, ?_⟩
  rw [hcard, hi, ← pow_mul, show (16 : ℕ) = 2 ^ 4 by norm_num] at hle
  have h1 : 4 ≤ i * m := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
  have h2 : 4 * r ≤ i * m * r := Nat.mul_le_mul_right r h1
  have h3 : i * m * r ≤ i * 6 := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left i hmr
  omega

theorem card_le_index [Finite S] (C : Ctx G L) (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤)
    (hcard : Nat.card S = 16) {B : Subgroup (MulAut S)} (hBG : B ≤ G) (hB1 : B ≠ ⊥)
    (hB : IsElemAbelian2 B) (h4 : Nat.card B ≤ 4) : Nat.card B ≤ (fixV B).index := by
  obtain ⟨r, i, hr, hi, hr1, -, h23⟩ := exists_rank C hirr hcard hBG hB1 hB
  rw [hr, hi]
  have hr2 : r ≤ 2 := by
    rw [hr] at h4
    by_contra h
    push Not at h
    have : 2 ^ 3 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) h
    omega
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem two_thirds_le_rAV [Finite S] (C : Ctx G L) (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤)
    (hcard : Nat.card S = 16) {B : Subgroup (MulAut S)} (hBG : B ≤ G) (hB1 : B ≠ ⊥)
    (hB : IsElemAbelian2 B) : (2 / 3 : ℚ) ≤ rAV B := by
  obtain ⟨r, i, hr, hi, hr1, -, h23⟩ := exists_rank C hirr hcard hBG hB1 hB
  have hrk : rk B = r := by
    unfold rk
    rw [hr]
    exact padicValNat.prime_pow r
  have hrkI : rkIdx (fixV B) = i := by
    unfold rkIdx
    rw [hi]
    exact padicValNat.prime_pow i
  unfold rAV
  rw [hrk, hrkI, le_div_iff₀ (by exact_mod_cast hr1)]
  have : (2 * r : ℚ) ≤ 3 * i := by exact_mod_cast h23
  linarith

theorem not_comm_of_card_eight (D : Subgroup (alternatingGroup (Fin 6))) (hD : Nat.card D = 8) :
    ∃ a b : ↥D, a * b ≠ b * a := by
  obtain ⟨e⟩ := DoubleA3.nonempty_dihedral_of_card_eight D hD
  refine ⟨e.symm (DihedralGroup.r 1), e.symm (DihedralGroup.sr 0), fun h => ?_⟩
  have h1 := congrArg e h
  simp only [map_mul, MulEquiv.apply_symm_apply] at h1
  exact absurd h1 (by decide)

theorem card_le_four_of_le_L (C : Ctx G L) {B : Subgroup (MulAut S)} (hBL : B ≤ L)
    (hB : IsElemAbelian2 B) {r : ℕ} (hr : Nat.card B = 2 ^ r) (hr3 : r ≤ 3) : r ≤ 2 := by
  by_contra h
  have hr8 : Nat.card B = 8 := by rw [hr, show r = 3 by omega]; norm_num
  obtain ⟨ι⟩ := C.iso
  set D : Subgroup (alternatingGroup (Fin 6)) := (B.subgroupOf L).map ι.toMonoidHom with hD
  have hDc : Nat.card D = 8 := by
    rw [hD, Subgroup.card_map_of_injective ι.injective, ← hr8]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  obtain ⟨⟨_, ⟨a, ha, rfl⟩⟩, ⟨_, ⟨b, hb, rfl⟩⟩, hab⟩ := not_comm_of_card_eight D hDc
  apply hab
  apply Subtype.ext
  show ι a * ι b = ι b * ι a
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hB.1 _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb))

end B42Alt6

end CFSG.Quasithin
