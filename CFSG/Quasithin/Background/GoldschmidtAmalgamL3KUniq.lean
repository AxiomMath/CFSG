module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Str

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3K

open GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z z' : D} {V V' : Subgroup D}

theorem conj_mem_pCoreOf_left (h : GoldHyp3 A B z V) {u g : D} (hu : u ∈ conjClosure V B)
    (hg : g ∈ A) : g * u * g⁻¹ ∈ pCoreOf 2 A :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 A hg) u).mp
    (h.conjClosure_le_pCoreOf_left hu)

theorem comm_conj_of_inf_eq_bot (h : GoldHyp3 A B z V) (h' : GoldHyp3 A B z' V')
    (hU : Nat.card (conjClosure V B) = 8) (hU' : Nat.card (conjClosure V' B) = 8)
    (hVV' : V ⊓ V' = ⊥) {u u' g : D} (hu : u ∈ conjClosure V B)
    (hu' : u' ∈ conjClosure V' B) (hg : g ∈ A) :
    u' * (g * u * g⁻¹) = (g * u * g⁻¹) * u' := by
  have hq : g * u * g⁻¹ ∈ pCoreOf 2 A := conj_mem_pCoreOf_left h hu hg
  have hw : g⁻¹ * u' * g ∈ pCoreOf 2 A := by
    have := conj_mem_pCoreOf_left h' hu' (A.inv_mem hg)
    simpa using this
  have h1 : u' * (g * u * g⁻¹) * u'⁻¹ * (g * u * g⁻¹)⁻¹ ∈ V' :=
    h'.commutator_mem_V_of_pCoreOf_left hU' hu' hq
  have h2 : u * (g⁻¹ * u' * g) * u⁻¹ * (g⁻¹ * u' * g)⁻¹ ∈ V :=
    h.commutator_mem_V_of_pCoreOf_left hU hu hw
  have h3 : u' * (g * u * g⁻¹) * u'⁻¹ * (g * u * g⁻¹)⁻¹ ∈ V := by
    have e : u' * (g * u * g⁻¹) * u'⁻¹ * (g * u * g⁻¹)⁻¹ =
        g * (u * (g⁻¹ * u' * g) * u⁻¹ * (g⁻¹ * u' * g)⁻¹)⁻¹ * g⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (h.natural.reduced.2.1 hg) _).mp (V.inv_mem h2)
  have h4 : u' * (g * u * g⁻¹) * u'⁻¹ * (g * u * g⁻¹)⁻¹ ∈ (⊥ : Subgroup D) := by
    rw [← hVV']
    exact Subgroup.mem_inf.mpr ⟨h3, h1⟩
  have h5 := Subgroup.mem_bot.mp h4
  rw [mul_inv_eq_one] at h5
  calc u' * (g * u * g⁻¹) = u' * (g * u * g⁻¹) * u'⁻¹ * u' := by group
    _ = (g * u * g⁻¹) * u' := by rw [h5]

theorem conjClosure_conjClosure_le_coreIn_of_inf_eq_bot (h : GoldHyp3 A B z V)
    (h' : GoldHyp3 A B z' V') (hU : Nat.card (conjClosure V B) = 8)
    (hU' : Nat.card (conjClosure V' B) = 8) (hVV' : V ⊓ V' = ⊥) :
    conjClosure (conjClosure V B) A ≤ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B := by
  refine conjClosure_le fun g hg u hu => ?_
  exact h'.mem_coreIn_of_comm (conj_mem_pCoreOf_left h hu hg) fun u' hu' =>
    comm_conj_of_inf_eq_bot h h' hU hU' hVV' hu hu' hg

theorem four_le_critDist_of_inf_eq_bot (h : GoldHyp3 A B z V) (h' : GoldHyp3 A B z' V')
    (hU : Nat.card (conjClosure V B) = 8) (hU' : Nat.card (conjClosure V' B) = 8)
    (hVV' : V ⊓ V' = ⊥) : 4 ≤ critDist (A ⊔ B) A B V :=
  h.four_le_critDist_iff_le_coreIn.mpr
    (conjClosure_conjClosure_le_coreIn_of_inf_eq_bot h h' hU hU' hVV')

theorem inf_ne_bot_of_critDist_eq_three (h : GoldHyp3 A B z V) (h' : GoldHyp3 A B z' V')
    (hU : Nat.card (conjClosure V B) = 8) (hU' : Nat.card (conjClosure V' B) = 8)
    (hb : critDist (A ⊔ B) A B V = 3) : V ⊓ V' ≠ ⊥ := fun hVV' => by
  have := four_le_critDist_of_inf_eq_bot h h' hU hU' hVV'
  omega

end GoldAmL3K

end F6

end CFSG.Quasithin
