module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9LemEProofIrr
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.Quasithin
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem lemE_conj_mem {H : Subgroup G} {g h : G} (hg : g ∈ Subgroup.normalizer (H : Set G))
    (hh : h ∈ H) : g * h * g⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.1 hg h).1 hh

theorem lemE_conj_mem_centralizer {L : Subgroup G} {y w : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) (hw : w ∈ Subgroup.centralizer (L : Set G)) :
    y * w * y⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : y⁻¹ * l * y ∈ L := by
    have := lemE_conj_mem ((Subgroup.normalizer (L : Set G)).inv_mem hy) hl
    simpa using this
  have h := Subgroup.mem_centralizer_iff.1 hw _ hl'
  calc l * (y * w * y⁻¹) = y * ((y⁻¹ * l * y) * w) * y⁻¹ := by group
    _ = y * (w * (y⁻¹ * l * y)) * y⁻¹ := by rw [h]
    _ = y * w * y⁻¹ * l := by group

theorem lemE_isElemAbelian_of_le {p : ℕ} {E X : Subgroup G} (hE : IsElemAbelian p E)
    (hXE : X ≤ E) : IsElemAbelian p X := CFSG.Open.IsElemAbelian.mono hE hXE

theorem lemE_le_oTwoUpper {Y X : Subgroup G} (hY : IsPGroup 5 Y) (hYX : Y ≤ X) :
    Y ≤ oTwoUpper X := by
  intro y hy
  refine mem_oTwoUpper_of_odd (hYX hy) ?_
  obtain ⟨k, hk⟩ := hY ⟨y, hy⟩
  have h1 : orderOf y ∣ 5 ^ k := by
    have := orderOf_dvd_of_pow_eq_one hk
    rwa [Subgroup.orderOf_mk] at this
  exact Odd.of_dvd_nat (Odd.pow (by decide)) h1

theorem lemE_comm_of_inf_eq_bot {V L S : Subgroup G} (hSV : S ≤ Subgroup.normalizer (V : Set G))
    (hVL : V ≤ Subgroup.normalizer (L : Set G)) (hbot : V ⊓ L = ⊥) {v x : G} (hv : v ∈ V)
    (hxS : x ∈ S) (hxL : x ∈ L) : v * x = x * v := by
  have h1 : v * x * v⁻¹ * x⁻¹ ∈ V ⊓ L := by
    refine ⟨?_, ?_⟩
    · have h2 : x * v⁻¹ * x⁻¹ ∈ V := lemE_conj_mem (hSV hxS) (V.inv_mem hv)
      have h3 := V.mul_mem hv h2
      simpa [mul_assoc] using h3
    · exact L.mul_mem (lemE_conj_mem (hVL hv) hxL) (L.inv_mem hxL)
  rw [hbot, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem lemE_inf_eq_bot_or_le [Finite G] {V Y L : Subgroup G} (hV : Nat.card V = 16)
    (hY : IsPGroup 5 Y) (hYV : Y ≤ Subgroup.normalizer (V : Set G)) (hVY : ⁅V, Y⁆ = V)
    (hYL : Y ≤ Subgroup.normalizer (L : Set G)) : V ⊓ L = ⊥ ∨ V ≤ L := by
  rcases eq_bot_or_eq_of_five (W := V ⊓ L) hV hY (fun y hy v hv => lemE_conj_mem (hYV hy) hv) hVY
      (fun y hy w hw => ⟨lemE_conj_mem (hYV hy) hw.1, lemE_conj_mem (hYL hy) hw.2⟩)
      inf_le_left with h | h
  · exact Or.inl h
  · exact Or.inr (inf_eq_left.1 h)

theorem lemE_inf_center_eq_bot [Finite G] {V Y L : Subgroup G} (hV : Nat.card V = 16)
    (hY : IsPGroup 5 Y) (hYV : Y ≤ Subgroup.normalizer (V : Set G)) (hVY : ⁅V, Y⁆ = V)
    (hYL : Y ≤ Subgroup.normalizer (L : Set G)) (hcomm : ⁅L, V⁆ ≠ ⊥) :
    V ⊓ (L ⊓ Subgroup.centralizer (L : Set G)) = ⊥ := by
  rcases eq_bot_or_eq_of_five (W := V ⊓ (L ⊓ Subgroup.centralizer (L : Set G))) hV hY
      (fun y hy v hv => lemE_conj_mem (hYV hy) hv) hVY
      (fun y hy w hw => ⟨lemE_conj_mem (hYV hy) hw.1, lemE_conj_mem (hYL hy) hw.2.1,
        lemE_conj_mem_centralizer (hYL hy) hw.2.2⟩) inf_le_left with h | h
  · exact h
  · exfalso
    apply hcomm
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 ((inf_eq_left.1 h).trans inf_le_right)

theorem lemE_exists_ne_one [Finite G] {V P : Subgroup G} (hV : Nat.card V = 16)
    (hP : IsPGroup 2 P) (hPV : ∀ y ∈ P, ∀ w ∈ V, y * w * y⁻¹ ∈ V) :
    ∃ x ∈ V, x ≠ 1 ∧ x ∈ Subgroup.centralizer (P : Set G) := by
  have hmod := card_modEq_card_inf_centralizer (p := 2) hP hPV
  rw [hV] at hmod
  have hne : V ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hmod
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  exact ⟨a.1, a.2.1, fun h => ha (Subtype.ext h), a.2.2⟩

end CFSG.Quasithin.E9
