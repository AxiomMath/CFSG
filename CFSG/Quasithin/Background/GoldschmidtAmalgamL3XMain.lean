module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3XBi
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3XChain
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3UMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace TypeIConfig

variable {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (c : TypeIConfig V m p)

include c

theorem false_of_typeI (h : GoldHyp3 A B z V) : False := by
  have hm6 := c.six_le
  obtain ⟨k, hk⟩ := c.even
  by_cases hBi : Vn V 2 (p 0) ≤ ballStab 1 (p m)
  · exact c.false_of_Bi h hBi
  · have htwin := c.twin h hBi
    have hcases : m = 6 ∨ m = 8 ∨ 10 ≤ m := by omega
    rcases hcases with rfl | rfl | hm10
    · exact h.Zv_ne_four (c.adj' (i := 1) (j := 2) rfl (by omega))
        (c.adj' (i := 2) (j := 3) rfl (by omega)) (c.adj' (i := 3) (j := 4) rfl (by omega))
        (c.adj' (i := 4) (j := 5) rfl (by omega)) (c.vtype_even (by omega) (by decide))
        (c.geo.ne (by omega) (by omega)) (c.geo.ne (by omega) (by omega)) htwin
    · exact h.Zv_ne_six c.card (c.adj' (i := 1) (j := 2) rfl (by omega))
        (c.adj' (i := 2) (j := 3) rfl (by omega)) (c.adj' (i := 3) (j := 4) rfl (by omega))
        (c.adj' (i := 4) (j := 5) rfl (by omega)) (c.adj' (i := 5) (j := 6) rfl (by omega))
        (c.adj' (i := 6) (j := 7) rfl (by omega)) (c.vtype_even (by omega) (by decide))
        (c.geo.ne (by omega) (by omega)) (c.geo.ne (by omega) (by omega))
        (c.geo.ne (by omega) (by omega)) htwin
    · exact c.false_of_BR_large h hBi hm10

end TypeIConfig

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

omit [Finite D] in
theorem Vv_smul_le_ballStab_smul_iff (g : ↥(A ⊔ B)) (x y : CosetGeom (A ⊔ B) A B) (n : ℕ) :
    Vv V (g • x) ≤ ballStab n (g • y) ↔ Vv V x ≤ ballStab n y := by
  rw [Vv_smul h.natural.reduced.2.1, ballStab_smul]
  refine ⟨fun hle => ?_, conjSub_mono _⟩
  have := (conjSub_le_iff (g : D)).mp hle
  rwa [conjSub_conjSub_inv] at this

theorem false_of_typeI_norm {m : ℕ} (hU : Nat.card (conjClosure V B) = 8)
    (hb : critDist (A ⊔ B) A B V = m + 1) (hm : 6 ≤ m) (hev : Even m)
    {p : ℕ → CosetGeom (A ⊔ B) A B} (hp0 : p 0 = γ₀ (A ⊔ B) A B) (hp : IsGeo p (m + 1))
    (hcrit : ¬ V ≤ ballStab 1 (p (m + 1)))
    (hgood : ∀ v, (graph (A ⊔ B) A B).Adj (p 0) v → Vv V v ≤ ballStab 1 (p (m - 1)))
    (hI : Vv V (p (m + 1)) ≤ ballStab 1 (p 1)) : False :=
  TypeIConfig.false_of_typeI (m := m) (p := p) ⟨hU, hb, hm, hev, hp0, hp, hcrit, hgood, hI⟩ h

theorem false_of_typeI {m : ℕ} (hU : Nat.card (conjClosure V B) = 8)
    (hb : critDist (A ⊔ B) A B V = m + 1) (hm : 6 ≤ m) (hev : Even m)
    {p : ℕ → CosetGeom (A ⊔ B) A B} (hp : IsGeo p (m + 1)) (hp0 : vtype (p 0) = false)
    (hcrit : ¬ Vv V (p 0) ≤ ballStab 1 (p (m + 1)))
    (hgood : ∀ v, (graph (A ⊔ B) A B).Adj (p 0) v → Vv V v ≤ ballStab 1 (p (m - 1)))
    (hI : Vv V (p (m + 1)) ≤ ballStab 1 (p 1)) : False := by
  obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hp0
  have hiff : ∀ (x y : CosetGeom (A ⊔ B) A B) (n : ℕ),
      Vv V (g⁻¹ • x) ≤ ballStab n (g⁻¹ • y) ↔ Vv V x ≤ ballStab n y :=
    fun x y n => h.Vv_smul_le_ballStab_smul_iff g⁻¹ x y n
  have h0 : g⁻¹ • p 0 = γ₀ (A ⊔ B) A B := by rw [hg, inv_smul_smul]
  refine h.false_of_typeI_norm (p := fun i => g⁻¹ • p i) hU hb hm hev h0
    (fun i j hij hj => by
      show CosetGeom.dist (g⁻¹ • p i) (g⁻¹ • p j) = j - i
      rw [CosetGeom.dist_smul]
      exact hp i j hij hj) ?_ ?_ ?_
  · intro hle
    apply hcrit
    have hV0 : Vv V (g⁻¹ • p 0) = V := by
      rw [h0]
      exact Vv_γ₀ h.natural.reduced.2.1
    exact (hiff (p 0) (p (m + 1)) 1).mp (by rw [hV0]; exact hle)
  · intro v hv
    have hv0 : (graph (A ⊔ B) A B).Adj (g⁻¹ • p 0) v := hv
    have hadj : (graph (A ⊔ B) A B).Adj (p 0) (g • v) := by
      have := (smul_adj g).mpr hv0
      rwa [smul_inv_smul] at this
    have := (hiff (g • v) (p (m - 1)) 1).mpr (hgood (g • v) hadj)
    rwa [inv_smul_smul] at this
  · exact (hiff _ _ _).mpr hI

theorem exists_good_typeII {m : ℕ} (hU : Nat.card (conjClosure V B) = 8)
    (hb : critDist (A ⊔ B) A B V = m + 1) (hm : 6 ≤ m) (hev : Even m) :
    ∃ p : ℕ → CosetGeom (A ⊔ B) A B, IsGeo p (m + 1) ∧ vtype (p 0) = false ∧
      ¬ Vv V (p 0) ≤ ballStab 1 (p (m + 1)) ∧
      (∀ v, (graph (A ⊔ B) A B).Adj (p 0) v → Vv V v ≤ ballStab 1 (p (m - 1))) ∧
      ¬ Vv V (p (m + 1)) ≤ ballStab 1 (p 1) := by
  obtain ⟨p, hp, hp0, hcrit, hgood⟩ := h.exists_good_crit_geodesic_any hU hb hm hev
  exact ⟨p, hp, hp0, hcrit, hgood, fun hI => h.false_of_typeI hU hb hm hev hp hp0 hcrit hgood hI⟩

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
