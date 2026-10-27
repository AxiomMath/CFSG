module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3UF30
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3UExt
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RCoinc
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RInj

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem false_of_crit_chain {m : ℕ} (hU : Nat.card (conjClosure V B) = 8)
    (hb : critDist (A ⊔ B) A B V = m + 1) (hm : 6 ≤ m) (hev : Even m)
    {p q r : ℕ → CosetGeom (A ⊔ B) A B}
    (hp : IsGeo p (m + 1)) (hq : IsGeo q (m + 1)) (hr : IsGeo r (m + 1))
    (hp0 : vtype (p 0) = false) (hq0 : vtype (q 0) = false) (hr0 : vtype (r 0) = false)
    (hpc : ¬ Vv V (p 0) ≤ ballStab 1 (p (m + 1)))
    (hqc : ¬ Vv V (q 0) ≤ ballStab 1 (q (m + 1)))
    (hrc : ¬ Vv V (r 0) ≤ ballStab 1 (r (m + 1)))
    (hqp : ∀ i, q (i + 2) = p i) (hrq : ∀ i, r (i + 2) = q i)
    {w : CosetGeom (A ⊔ B) A B} (hw : (graph (A ⊔ B) A B).Adj (r 0) w)
    (hwbad : ¬ Vv V w ≤ ballStab 1 (r (m - 1))) : False := by
  have hrm : r (m - 1) = p (m - 5) := by
    have e1 := hrq (m - 3)
    have e2 := hqp (m - 5)
    rw [show m - 3 + 2 = m - 1 by omega] at e1
    rw [show m - 5 + 2 = m - 3 by omega] at e2
    rw [e1, e2]
  have hqm : q (m + 1) = p (m - 1) := by
    have := hqp (m - 1)
    rwa [show m - 1 + 2 = m + 1 by omega] at this
  have hq2 : q 2 = p 0 := hqp 0
  have hq3 : q 3 = p 1 := hqp 1
  have hF : Zv z (p (m - 5)) ≤ Vv V (q 0) := by
    have := h.Zv_le_Vv_of_bad_neighbour hU hb (by omega) hev hr hr0 hrc hw hwbad
    rwa [hrm, hrq 0] at this
  have h5t : vtype (p (m - 5)) = true := hp.vtype_true_of_odd_start rfl hp0 (by omega) (by
    obtain ⟨k, hk⟩ := hev
    exact ⟨k - 3, by omega⟩)
  have h1p : vtype (p 1) = true := hp.vtype_true_of_odd_start rfl hp0 (by omega) (by decide)
  have h1q : vtype (q 1) = true := hq.vtype_true_of_odd_start rfl hq0 (by omega) (by decide)
  obtain ⟨c, hcZ, hc1⟩ := h.exists_ne_one_mem_Zv h5t
  have hcQ4 : c ∈ ballStab 1 (q (m + 1)) := by
    rw [hqm]
    exact h.Zv_le_ballStab_one_of_dist_le hb h5t
      (by rw [hp (m - 5) (m - 1) (by omega) (by omega)]; omega) hcZ
  have hcQ6 : c ∈ ballStab 1 (p (m + 1)) :=
    h.Zv_le_ballStab_one_of_dist_le hb h5t
      (by rw [hp (m - 5) (m + 1) (by omega) le_rfl]; omega) hcZ
  have hcq : c ∈ Zv z (q 1) :=
    h.mem_Zv_of_mem_Vv_of_mem_ballStab hb hq hq0 hqc (hF hcZ) hcQ4
  have a21 : (graph (A ⊔ B) A B).Adj (q 2) (q 1) := (hq.adj (i := 1) (by omega)).symm
  have hcp0 : c ∈ Vv V (p 0) := by
    have := h.Zv_le_Vv a21 (by rw [hq2]; exact hp0) hcq
    rwa [hq2] at this
  have hcp : c ∈ Zv z (p 1) :=
    h.mem_Zv_of_mem_Vv_of_mem_ballStab hb hp hp0 hpc hcp0 hcQ6
  have hzz : Zv z (q 1) = Zv z (p 1) := h.Zv_eq_of_mem h1q h1p hcq hcp hc1
  have hq1 : q 1 = p 1 := by
    refine h.eq_of_Zv_eq hp0 ?_ (hp.adj (i := 0) (by omega)) hzz
    rw [← hq2]
    exact a21
  exact hq.ne (i := 1) (j := 3) (by omega) (by omega) (by rw [hq3]; exact hq1)

theorem exists_good_crit_geodesic_any {m : ℕ} (hU : Nat.card (conjClosure V B) = 8)
    (hb : critDist (A ⊔ B) A B V = m + 1) (hm : 6 ≤ m) (hev : Even m) :
    ∃ p : ℕ → CosetGeom (A ⊔ B) A B, IsGeo p (m + 1) ∧ vtype (p 0) = false ∧
      ¬ Vv V (p 0) ≤ ballStab 1 (p (m + 1)) ∧
      ∀ v, (graph (A ⊔ B) A B).Adj (p 0) v → Vv V v ≤ ballStab 1 (p (m - 1)) := by
  by_contra hne
  push Not at hne
  obtain ⟨p, hp0, hp, hpc⟩ := h.exists_crit_geodesic hb
  have hp0t : vtype (p 0) = false := by
    rw [hp0]
    exact vtype_γ₀
  have hpc' : ¬ Vv V (p 0) ≤ ballStab 1 (p (m + 1)) := by
    rw [hp0, Vv_γ₀ h.natural.reduced.2.1]
    exact hpc
  obtain ⟨v₁, hv₁, hbad₁⟩ := hne p hp hp0t hpc'
  obtain ⟨q, hq, hq0, hqc, -, hqp⟩ := h.exists_crit_ext hb (by omega) hp hp0t hv₁ hbad₁
  obtain ⟨v₂, hv₂, hbad₂⟩ := hne q hq hq0 hqc
  obtain ⟨r, hr, hr0, hrc, -, hrq⟩ := h.exists_crit_ext hb (by omega) hq hq0 hv₂ hbad₂
  obtain ⟨w, hw, hwbad⟩ := hne r hr hr0 hrc
  exact h.false_of_crit_chain hU hb hm hev hp hq hr hp0t hq0 hr0 hpc' hqc hrc hqp hrq hw hwbad

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
