module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3S9Rank
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3WTwoMain
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SCard
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3WTwoGood
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3YNA
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3ZEven
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3ZTypeI

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace OddCritG

variable {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (c : OddCritG V m p) (h : GoldHyp3 A B z V)

include c h

theorem false_of_typeII_sixteen_of_I2a (hU : Nat.card (conjClosure V B) = 16)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false →
      (graph (A ⊔ B) A B).Adj u β → (graph (A ⊔ B) A B).Adj u β' → β ≠ β' →
        Vv V β ⊓ Vv V β' ≤ Vv V u)
    (hI2a : I2aProp A B V)
    (hnon : Vn V 2 (p 0) ≤ ballStab 1 (p m))
    (hII : ¬ Vv V (p (m + 1)) ≤ ballStab 1 (p 1)) : False := by
  have hm := c.six_le
  have hb := c.crit_eq
  have hbt : vtype (p (m + 1)) = true := c.vtype_odd le_rfl c.even.add_one
  have hat : vtype (p m) = false := c.vtype_even (by omega) c.even
  obtain ⟨y, hyV, hyQ⟩ := IsConcreteLE.not_le_iff_exists.1 hII
  have hy2 : y ∈ ballStab 1 (p 2) := by
    refine h.VvB_le_ballStab_one_of_dist hb hbt ?_ hyV
    rw [CosetGeom.dist_comm, c.dist_eq (i := 2) (j := m + 1) (by omega) le_rfl]
    omega
  have hy2s : y ∈ stab (p 2) := ballStab_le_stab 1 _ hy2
  have hy1 : y ∈ stab (p 1) := by
    refine ballStab_le_stab_of_dist_le (n := 1) ?_ hy2
    rw [CosetGeom.dist_comm, c.dist_eq (i := 1) (j := 2) (by omega) (by omega)]
  have h10 : (graph (A ⊔ B) A B).Adj (p 1) (p 0) := (c.adj (i := 0) (by omega)).symm
  have h12 : (graph (A ⊔ B) A B).Adj (p 1) (p 2) := c.adj (i := 1) (by omega)
  have hy0 : y ∉ stab (p 0) := fun hy0 =>
    hyQ (h.mem_ballStab_one_of_fix_two' h10 h12 (c.ne (i := 0) (j := 2) (by omega) (by omega))
      hy1 hy0 hy2s)
  refine h.false_of_comm_mem_card_le_B_of_I2a hU hI1 hI2a c.vtype_zero
    (c.adj (i := 0) (by omega)) hy1 hy0
    (P := Theta z V (p m) (p (m + 1))) (h.card_Theta_le_four hat (c.adj le_rfl)) ?_
  intro w hw
  have hwm : w ∈ ballStab 1 (p m) := hnon hw
  refine comm_mem_Theta ⟨ballStab_le_stab 1 _ hwm, ?_⟩ hyV z
  refine ballStab_le_stab_of_dist_le (n := 1) ?_ hwm
  rw [c.dist_eq (i := m) (j := m + 1) (by omega) le_rfl]
  omega

end OddCritG

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem false_of_odd_critDist_sixteen_of_I2a (hU : Nat.card (conjClosure V B) = 16)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false →
      (graph (A ⊔ B) A B).Adj u β → (graph (A ⊔ B) A B).Adj u β' → β ≠ β' →
        Vv V β ⊓ Vv V β' ≤ Vv V u)
    (hI2a : I2aProp A B V)
    {m : ℕ} (hb : critDist (A ⊔ B) A B V = m + 1) (hm : 6 ≤ m) (hme : Even m) : False := by
  obtain ⟨p, hp0, hgeo, hnle⟩ := h.exists_crit_geodesic hb
  have c : OddCritG V m p := ⟨hb, hm, hme, hp0, hgeo, hnle⟩
  have hgood := c.Vn_two_le_ballStab_pred h hU hI1 hI2a
  have hnon := c.Vn_two_le_ballStab_last h hU hI1 hgood
  by_cases hI : Vv V (p (m + 1)) ≤ ballStab 1 (p 1)
  · exact TypeIConfigG.false_of_typeI
      ⟨hb, hm, hme, hp0, hgeo, hnle,
        fun v hv => (Vv_B_le_Vn_two c.vtype_zero hv).trans hgood, hI⟩ h hU hI1
  · exact c.false_of_typeII_sixteen_of_I2a h hU hI1 hI2a hnon hI

theorem false_of_seven_le_critDist_sixteen_of_I2a (hU : Nat.card (conjClosure V B) = 16)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false →
      (graph (A ⊔ B) A B).Adj u β → (graph (A ⊔ B) A B).Adj u β' → β ≠ β' →
        Vv V β ⊓ Vv V β' ≤ Vv V u)
    (hI2a : I2aProp A B V) (hb : 7 ≤ critDist (A ⊔ B) A B V) : False := by
  obtain ⟨m, hm⟩ : ∃ m, critDist (A ⊔ B) A B V = m + 1 :=
    ⟨critDist (A ⊔ B) A B V - 1, by omega⟩
  rcases Nat.even_or_odd m with hme | hmo
  · exact h.false_of_odd_critDist_sixteen_of_I2a hU hI1 hI2a hm (by omega) hme
  · obtain ⟨k, hk⟩ := hmo
    obtain ⟨p, hp0, hgeo, hnle⟩ := h.exists_crit_geodesic hm
    exact EvenCritG.false_of_even h ⟨hm, by omega, ⟨k, hk⟩, hgeo, hp0, hnle⟩ hU hI1

theorem false_of_seven_le_critDist_sixteen_of_I2a' (hA : NoACentral A B)
    (hU : Nat.card (conjClosure V B) = 16) (hI2a : I2aProp A B V)
    (hb : 7 ≤ critDist (A ⊔ B) A B V) : False :=
  h.false_of_seven_le_critDist_sixteen_of_I2a hU (h.I1_of_noACentral hA hU) hI2a hb

end GoldHyp3

theorem b7CardInput_of_noACentral_I2a (hA : B7NoACInput.{u}) (ha : B7I2aInput.{u}) :
    B7CardInput.{u} := by
  intro D _ _ A B z V h hcrit
  rcases h.card_conjClosure_eq with h8 | h16
  · exact h8
  · have hA' := hA D A B z V h hcrit h16
    exact (h.false_of_seven_le_critDist_sixteen_of_I2a' hA' h16
      (ha D A B z V h hA' hcrit h16) hcrit).elim

end GoldAmL3

end F6

end CFSG.Quasithin
