module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3XBR

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

theorem Vn_four_comm (h : GoldHyp3 A B z V) :
    Vn V 4 (p 0) ≤ Subgroup.centralizer (Vn V 2 (p 0) : Set D) :=
  h.Vn_le_centralizer_Vn c.critDist_eq (n := 4) (n' := 2)
    (by rw [CosetGeom.dist_self]; have := c.six_le; omega)

theorem Vn_four_le (h : GoldHyp3 A B z V) (hBR : ¬ Vn V 2 (p 0) ≤ ballStab 1 (p m)) :
    Vn V 4 (p 0) ≤ ballStab 1 (p (m - 2)) := by
  have hb := c.critDist_eq
  have hm6 := c.six_le
  obtain ⟨k, hk⟩ := c.even
  have hHW := c.Vn_four_comm h
  have hcent : ∀ S : Subgroup D, S ≤ Vn V 2 (p 0) →
      S ≤ Subgroup.centralizer (Vn V 4 (p 0) : Set D) := fun S hS x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact ((Subgroup.mem_centralizer_iff.mp (hHW hg)) x (hS hx)).symm
  have hH0 : Vn V 4 (p 0) ≤ ballStab 1 (p (m - 4)) :=
    h.Vn_le_ballStab_one hb (by rw [c.dist_zero (by omega)]; omega)
  have hZ1 : Zv z (p (m - 1)) ≤ Vn V 2 (p 0) := by
    rw [← c.twin h hBR]
    exact c.Zv_one_le_Vn h
  have hne : p (m - 3) ≠ p (m - 1) := c.geo.ne (by omega) (by omega)
  have hc3 : Zv z (p (m - 3)) ≤ Subgroup.centralizer (Vn V 4 (p 0) : Set D) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hgs : g ∈ stab (p (m - 3)) := ballStab_le_stab_of_dist_le (n := 1)
      (dist_eq_one_iff_adj.mpr (c.adj' (i := m - 4) (j := m - 3) (by omega) (by omega))).le
      (hH0 hg)
    exact mul_inv_eq_iff_eq_mul.mp (h.stab_centralizes_Zv
      (c.vtype_odd (by omega) (⟨k - 2, by omega⟩ : Odd (m - 3))) hgs hx)
  have hV3 : Vv V (p (m - 2)) ≤ Subgroup.centralizer (Vn V 4 (p 0) : Set D) :=
    h.Vv_le_centralizer_of_two_labels
      (c.vtype_even (by omega) (⟨k - 1, by omega⟩ : Even (m - 2)))
      (c.adj' (i := m - 3) (j := m - 2) (by omega) (by omega)).symm
      (c.adj' (i := m - 2) (j := m - 1) (by omega) (by omega)) hne hc3 (hcent _ hZ1)
  have hH1 : Vn V 4 (p 0) ≤ ballStab 1 (p (m - 3)) := by
    have := c.desc h (j := m - 4) (by omega) hH0 (by
      rw [show m - 4 + 2 = m - 2 by omega, c.Zlab_even (by omega) ⟨k - 1, by omega⟩]
      exact Subgroup.le_centralizer_iff.mp hV3)
    rwa [show m - 4 + 1 = m - 3 by omega] at this
  have := c.desc h (j := m - 3) (by omega) hH1 (by
    rw [show m - 3 + 2 = m - 1 by omega, c.Zlab_odd (by omega) ⟨k - 1, by omega⟩]
    exact Subgroup.le_centralizer_iff.mp (hcent _ hZ1))
  rwa [show m - 3 + 1 = m - 2 by omega] at this

theorem commutator_of_correction (h : GoldHyp3 A B z V)
    (hBR : ¬ Vn V 2 (p 0) ≤ ballStab 1 (p m)) {a n : ℕ} (han : a ≤ n) (hn : n + 1 ≤ m)
    (hcomm : Vn V n (p 0) ≤ Subgroup.centralizer (Vn V a (p 0) : Set D))
    (hZa : Zv z (p (m - 1)) ≤ Vn V a (p 0)) {u : D} (huV : u ∈ Vv V (p (m + 1)))
    (hu0 : u ∈ stab (p 0))
    (hcorr : ∀ w ∈ Vn V n (p 0), ∃ g ∈ Vn V a (p 0), w * g⁻¹ ∈ ballStab 1 (p m)) :
    ∀ w ∈ Vn V n (p 0), u * w * u⁻¹ * w⁻¹ ∈ Vn V a (p 0) := by
  have hm6 := c.six_le
  have hmt : vtype (p m) = false := c.vtype_even (by omega) c.even
  have hadj : (graph (A ⊔ B) A B).Adj (p m) (p (m + 1)) := c.adj le_rfl
  intro w hw
  obtain ⟨g, hgA, hwg⟩ := hcorr w hw
  have hgn : g ∈ Vn V n (p 0) := Vn_mono han (p 0) hgA
  have hw'' : w * g⁻¹ ∈ Vn V n (p 0) := (Vn V n (p 0)).mul_mem hw ((Vn V n (p 0)).inv_mem hgn)
  have hwQ : w * g⁻¹ ∈ stab (p m) ⊓ stab (p (m + 1)) :=
    ⟨ballStab_le_stab 1 _ hwg,
      ballStab_le_stab_of_dist_le (n := 1) (dist_eq_one_iff_adj.mpr hadj).le hwg⟩
  have hnorm : ∀ x ∈ Vn V n (p 0), u * x * u⁻¹ ∈ Vn V n (p 0) := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (h.stab_le_normalizer_Vn n (p 0) hu0) x).mp hx
  have hnorma : ∀ x ∈ Vn V a (p 0), u * x * u⁻¹ ∈ Vn V a (p 0) := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (h.stab_le_normalizer_Vn a (p 0) hu0) x).mp hx
  have h1 : u * (w * g⁻¹) * u⁻¹ * (w * g⁻¹)⁻¹ ∈ Vn V a (p 0) := by
    have hV : u * (w * g⁻¹) * u⁻¹ * (w * g⁻¹)⁻¹ ∈ Vv V (p m) := by
      have := h.commutator_mem_Vv c.card hadj hmt hwQ huV
      have e : u * (w * g⁻¹) * u⁻¹ * (w * g⁻¹)⁻¹ =
          ((w * g⁻¹) * u * (w * g⁻¹)⁻¹ * u⁻¹)⁻¹ := by group
      rw [e]
      exact (Vv V (p m)).inv_mem this
    have hN : u * (w * g⁻¹) * u⁻¹ * (w * g⁻¹)⁻¹ ∈ Vn V n (p 0) :=
      (Vn V n (p 0)).mul_mem (hnorm _ hw'') ((Vn V n (p 0)).inv_mem hw'')
    exact hZa (c.Vn_inf_Vv_le h hBR hn hN hV)
  have h2 : (w * g⁻¹) * (u * g * u⁻¹ * g⁻¹) * (w * g⁻¹)⁻¹ ∈ Vn V a (p 0) := by
    have hx : u * g * u⁻¹ * g⁻¹ ∈ Vn V a (p 0) :=
      (Vn V a (p 0)).mul_mem (hnorma g hgA) ((Vn V a (p 0)).inv_mem hgA)
    have hcx := Subgroup.mem_centralizer_iff.mp (hcomm hw'') _ hx
    have e : (w * g⁻¹) * (u * g * u⁻¹ * g⁻¹) * (w * g⁻¹)⁻¹ = u * g * u⁻¹ * g⁻¹ := by
      rw [← hcx, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    exact hx
  have e : u * w * u⁻¹ * w⁻¹ = (u * (w * g⁻¹) * u⁻¹ * (w * g⁻¹)⁻¹) *
      ((w * g⁻¹) * (u * g * u⁻¹ * g⁻¹) * (w * g⁻¹)⁻¹) := by group
  rw [e]
  exact (Vn V a (p 0)).mul_mem h1 h2

theorem not_Vn_four_le (h : GoldHyp3 A B z V) (hBR : ¬ Vn V 2 (p 0) ≤ ballStab 1 (p m)) :
    ¬ Vn V 4 (p 0) ≤ ballStab 1 (p (m - 1)) := by
  intro hA2
  have hm6 := c.six_le
  have hadj : (graph (A ⊔ B) A B).Adj (p m) (p (m - 1)) :=
    c.adj_pred (i := m) (by omega) (by omega)
  have hQT : ∀ {w : D}, w ∈ ballStab 1 (p (m - 1)) → w ∈ stab (p m) ⊓ stab (p (m - 1)) :=
    fun hw => ⟨ballStab_le_stab_of_dist_le (n := 1) (dist_eq_one_iff_adj.mpr hadj.symm).le hw,
      ballStab_le_stab 1 _ hw⟩
  obtain ⟨u, huV, huT, huQ⟩ := c.exists_u h
  obtain ⟨g₀, hg₀W, hg₀Q⟩ := IsConcreteLE.not_le_iff_exists.1 hBR
  have hg₀T := hQT (c.Vn_two_le hg₀W)
  have hZa : Zv z (p (m - 1)) ≤ Vn V 2 (p 0) := by
    rw [← c.twin h hBR]
    exact c.Zv_one_le_Vn h
  refine c.false_of_acts_trivially h (a := 2) (b' := 3) (c' := 4) (by omega) (by omega)
    (by omega) huT huQ ?_
  refine c.commutator_of_correction h hBR (a := 2) (n := 4) (by omega) (by omega)
    (c.Vn_four_comm h) hZa huV huT.1 fun w hw => ?_
  by_cases hwQ : w ∈ ballStab 1 (p m)
  · exact ⟨1, one_mem _, by simpa using hwQ⟩
  · exact ⟨g₀, hg₀W, h.mul_inv_mem_ballStab_one hadj (hQT (hA2 hw)) hg₀T hwQ hg₀Q⟩

theorem Vv_le_Vn_four (h : GoldHyp3 A B z V) (hBR : ¬ Vn V 2 (p 0) ≤ ballStab 1 (p m))
    (hA2 : Vn V 4 (p 0) ≤ ballStab 1 (p (m - 2))) : Vv V (p (m - 2)) ≤ Vn V 4 (p 0) := by
  have hm6 := c.six_le
  obtain ⟨k, hk⟩ := c.even
  have hmt : vtype (p m) = false := c.vtype_even (by omega) c.even
  have hbt : vtype (p (m + 1)) = true := c.vtype_odd le_rfl c.even.add_one
  have hvm1 : vtype (p (m - 1)) = true := c.vtype_odd (by omega) ⟨k - 1, by omega⟩
  have hvm2 : vtype (p (m - 2)) = false := c.vtype_even (by omega) ⟨k - 1, by omega⟩
  have hadj : (graph (A ⊔ B) A B).Adj (p m) (p (m - 1)) :=
    c.adj_pred (i := m) (by omega) (by omega)
  have hadj2 : (graph (A ⊔ B) A B).Adj (p (m - 2)) (p (m - 1)) :=
    c.adj' (i := m - 2) (j := m - 1) (by omega) (by omega)
  obtain ⟨g₁, hg₁A, hg₁Q⟩ := IsConcreteLE.not_le_iff_exists.1 (c.not_Vn_four_le h hBR)
  have hg₁2 : g₁ ∈ ballStab 1 (p (m - 2)) := hA2 hg₁A
  have hg₁s2 : g₁ ∈ stab (p (m - 2)) := ballStab_le_stab 1 _ hg₁2
  have hg₁s1 : g₁ ∈ stab (p (m - 1)) :=
    ballStab_le_stab_of_dist_le (n := 1) (dist_eq_one_iff_adj.mpr hadj2).le hg₁2
  obtain ⟨u', hu'Z, hu'1⟩ := h.exists_ne_one_mem_Zv hbt
  have hu'V : u' ∈ Vv V (p m) := h.Zv_le_Vv (c.adj le_rfl) hmt hu'Z
  have hu'ne : u' ∉ Zv z (p (m - 1)) := fun hz => by
    have hZZ := eq_of_card_two_of_mem (h.card_Zv hbt) (h.card_Zv hvm1) hu'Z hz hu'1
    exact c.geo.ne (i := m - 1) (j := m + 1) (by omega) le_rfl
      (h.eq_of_Zv_eq hmt hadj (c.adj le_rfl) hZZ.symm)
  have hu'0 : u' ∈ stab (p 0) := ballStab_le_stab 1 _ (h.Vv_le_ballStab_one_of_dist
    c.critDist_eq hmt (by
      have := c.dist_zero (i := m) (by omega)
      rw [CosetGeom.dist_comm]
      omega) hu'V)
  have hu'1' : u' ∈ Vv V (p (m - 1)) := Vv_le_Vv_of_adj hadj hmt hu'V
  have hκX : g₁ * u' * g₁⁻¹ * u'⁻¹ ∈ Vv V (p (m - 2)) :=
    h.commutator_mem_Vv c.card hadj2 hvm2 ⟨hg₁s2, hg₁s1⟩ hu'1'
  have hκY : g₁ * u' * g₁⁻¹ * u'⁻¹ ∈ Vn V 4 (p 0) := by
    have hconj := (Subgroup.mem_normalizer_iff.mp (h.stab_le_normalizer_Vn 4 (p 0) hu'0)
      g₁⁻¹).mp ((Vn V 4 (p 0)).inv_mem hg₁A)
    have e : g₁ * u' * g₁⁻¹ * u'⁻¹ = g₁ * (u' * g₁⁻¹ * u'⁻¹) := by group
    rw [e]
    exact (Vn V 4 (p 0)).mul_mem hg₁A hconj
  have hκZ : g₁ * u' * g₁⁻¹ * u'⁻¹ ∉ Zv z (p (m - 1)) := by
    intro hκ
    have hg₁m : g₁ ∉ stab (p m) := fun hs => hg₁Q (h.mem_ballStab_one_of_fix_two hvm1
      hadj2.symm hadj.symm (c.geo.ne (i := m - 2) (j := m) (by omega) (by omega)) hg₁s1 hg₁s2 hs)
    lift g₁ to ↥(A ⊔ B) using stab_le _ hg₁s1 with g'
    have hg'1 : g' • p (m - 1) = p (m - 1) := smul_eq_of_mem_stab hg₁s1
    have hadj'' : (graph (A ⊔ B) A B).Adj (p (m - 1)) (g' • p m) := by
      have := (smul_adj g').mpr hadj.symm
      rwa [hg'1] at this
    have hne'' : p m ≠ g' • p m := fun e => hg₁m (mem_stab_of_smul_eq e.symm)
    have hconj1 : (g' : D) * u' * (g' : D)⁻¹ ∈ Vv V (p m) := by
      have e : (g' : D) * u' * (g' : D)⁻¹ = ((g' : D) * u' * (g' : D)⁻¹ * u'⁻¹) * u' := by group
      rw [e]
      exact (Vv V (p m)).mul_mem (h.Zv_le_Vv hadj hmt hκ) hu'V
    have hconj2 : (g' : D) * u' * (g' : D)⁻¹ ∈ Vv V (g' • p m) := by
      rw [Vv_smul h.natural.reduced.2.1 g' (p m)]
      exact mul_mem_conjSub hu'V
    have hζ : (g' : D) * u' * (g' : D)⁻¹ ∈ Zv z (p (m - 1)) :=
      h.mem_Zv_of_mem_Vv_of_mem_Vv hvm1 hadj.symm hadj'' hne'' hconj1 hconj2
    have h5 : ((g' : D))⁻¹ * ((g' : D) * u' * (g' : D)⁻¹) * (g' : D) =
        (g' : D) * u' * (g' : D)⁻¹ := by
      simpa using h.stab_centralizes_Zv hvm1 ((stab (p (m - 1))).inv_mem hg₁s1) hζ
    apply hu'ne
    have e : u' = (g' : D)⁻¹ * ((g' : D) * u' * (g' : D)⁻¹) * (g' : D) := by group
    rw [e, h5]
    exact hζ
  have hZY : Zv z (p (m - 1)) ≤ Vn V 4 (p 0) := by
    rw [← c.twin h hBR]
    exact (c.Zv_one_le_Vn h).trans (Vn_mono (by omega) (p 0))
  exact le_of_card_four (h.card_Vv_A hvm2) (h.card_Zv hvm1) (h.Zv_le_Vv hadj2 hvm2) hZY hκX hκY hκZ

theorem Vn_six_comm (h : GoldHyp3 A B z V) (hm10 : 10 ≤ m) :
    Vn V 6 (p 0) ≤ Subgroup.centralizer (Vn V 4 (p 0) : Set D) :=
  h.Vn_le_centralizer_Vn c.critDist_eq (n := 6) (n' := 4)
    (by rw [CosetGeom.dist_self]; omega)

theorem Vn_six_le (h : GoldHyp3 A B z V) (hBR : ¬ Vn V 2 (p 0) ≤ ballStab 1 (p m))
    (hm10 : 10 ≤ m) (hV3 : Vv V (p (m - 2)) ≤ Vn V 4 (p 0)) :
    Vn V 6 (p 0) ≤ ballStab 1 (p (m - 2)) := by
  have hb := c.critDist_eq
  obtain ⟨k, hk⟩ := c.even
  have hHA := c.Vn_six_comm h hm10
  have hcent : ∀ S : Subgroup D, S ≤ Vn V 4 (p 0) →
      S ≤ Subgroup.centralizer (Vn V 6 (p 0) : Set D) := fun S hS x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact ((Subgroup.mem_centralizer_iff.mp (hHA hg)) x (hS hx)).symm
  have hH0 : Vn V 6 (p 0) ≤ ballStab 1 (p (m - 6)) :=
    h.Vn_le_ballStab_one hb (by rw [c.dist_zero (by omega)]; omega)
  have hZ3 : Zv z (p (m - 3)) ≤ Vn V 4 (p 0) :=
    (h.Zv_le_Vv (c.adj' (i := m - 3) (j := m - 2) (by omega) (by omega)).symm
      (c.vtype_even (by omega) (⟨k - 1, by omega⟩ : Even (m - 2)))).trans hV3
  have hZ1 : Zv z (p (m - 1)) ≤ Vn V 4 (p 0) := by
    rw [← c.twin h hBR]
    exact (c.Zv_one_le_Vn h).trans (Vn_mono (by omega) (p 0))
  have hc5 : Zv z (p (m - 5)) ≤ Subgroup.centralizer (Vn V 6 (p 0) : Set D) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hgs : g ∈ stab (p (m - 5)) := ballStab_le_stab_of_dist_le (n := 1)
      (dist_eq_one_iff_adj.mpr (c.adj' (i := m - 6) (j := m - 5) (by omega) (by omega))).le
      (hH0 hg)
    exact mul_inv_eq_iff_eq_mul.mp (h.stab_centralizes_Zv
      (c.vtype_odd (by omega) (⟨k - 3, by omega⟩ : Odd (m - 5))) hgs hx)
  have hV5 : Vv V (p (m - 4)) ≤ Subgroup.centralizer (Vn V 6 (p 0) : Set D) :=
    h.Vv_le_centralizer_of_two_labels
      (c.vtype_even (by omega) (⟨k - 2, by omega⟩ : Even (m - 4)))
      (c.adj' (i := m - 5) (j := m - 4) (by omega) (by omega)).symm
      (c.adj' (i := m - 4) (j := m - 3) (by omega) (by omega))
      (c.geo.ne (by omega) (by omega)) hc5 (hcent _ hZ3)
  have hH1 : Vn V 6 (p 0) ≤ ballStab 1 (p (m - 5)) := by
    have := c.desc h (j := m - 6) (by omega) hH0 (by
      rw [show m - 6 + 2 = m - 4 by omega, c.Zlab_even (by omega) ⟨k - 2, by omega⟩]
      exact Subgroup.le_centralizer_iff.mp hV5)
    rwa [show m - 6 + 1 = m - 5 by omega] at this
  have hH2 : Vn V 6 (p 0) ≤ ballStab 1 (p (m - 4)) := by
    have := c.desc h (j := m - 5) (by omega) hH1 (by
      rw [show m - 5 + 2 = m - 3 by omega, c.Zlab_odd (by omega) ⟨k - 2, by omega⟩]
      exact Subgroup.le_centralizer_iff.mp (hcent _ hZ3))
    rwa [show m - 5 + 1 = m - 4 by omega] at this
  have hH3 : Vn V 6 (p 0) ≤ ballStab 1 (p (m - 3)) := by
    have := c.desc h (j := m - 4) (by omega) hH2 (by
      rw [show m - 4 + 2 = m - 2 by omega, c.Zlab_even (by omega) ⟨k - 1, by omega⟩]
      exact Subgroup.le_centralizer_iff.mp (hcent _ hV3))
    rwa [show m - 4 + 1 = m - 3 by omega] at this
  have := c.desc h (j := m - 3) (by omega) hH3 (by
    rw [show m - 3 + 2 = m - 1 by omega, c.Zlab_odd (by omega) ⟨k - 1, by omega⟩]
    exact Subgroup.le_centralizer_iff.mp (hcent _ hZ1))
  rwa [show m - 3 + 1 = m - 2 by omega] at this

theorem false_of_BR_large (h : GoldHyp3 A B z V) (hBR : ¬ Vn V 2 (p 0) ≤ ballStab 1 (p m))
    (hm10 : 10 ≤ m) : False := by
  have hm6 := c.six_le
  have hadj : (graph (A ⊔ B) A B).Adj (p m) (p (m - 1)) :=
    c.adj_pred (i := m) (by omega) (by omega)
  have hadj2 : (graph (A ⊔ B) A B).Adj (p (m - 1)) (p (m - 2)) :=
    (c.adj' (i := m - 2) (j := m - 1) (by omega) (by omega)).symm
  have hA2 := c.Vn_four_le h hBR
  have hV3 := c.Vv_le_Vn_four h hBR hA2
  have hA3 := c.Vn_six_le h hBR hm10 hV3
  have hQT : ∀ {w : D}, w ∈ ballStab 1 (p (m - 1)) → w ∈ stab (p m) ⊓ stab (p (m - 1)) :=
    fun hw => ⟨ballStab_le_stab_of_dist_le (n := 1) (dist_eq_one_iff_adj.mpr hadj.symm).le hw,
      ballStab_le_stab 1 _ hw⟩
  have hQT2 : ∀ {w : D}, w ∈ ballStab 1 (p (m - 2)) →
      w ∈ stab (p (m - 1)) ⊓ stab (p (m - 2)) := fun hw =>
    ⟨ballStab_le_stab_of_dist_le (n := 1) (dist_eq_one_iff_adj.mpr hadj2.symm).le hw,
      ballStab_le_stab 1 _ hw⟩
  obtain ⟨u, huV, huT, huQ⟩ := c.exists_u h
  obtain ⟨g₀, hg₀W, hg₀Q⟩ := IsConcreteLE.not_le_iff_exists.1 hBR
  obtain ⟨g₁, hg₁A, hg₁Q⟩ := IsConcreteLE.not_le_iff_exists.1 (c.not_Vn_four_le h hBR)
  have hg₀T := hQT (c.Vn_two_le hg₀W)
  have hg₁T := hQT2 (hA2 hg₁A)
  have hZa : Zv z (p (m - 1)) ≤ Vn V 4 (p 0) := by
    rw [← c.twin h hBR]
    exact (c.Zv_one_le_Vn h).trans (Vn_mono (by omega) (p 0))
  refine c.false_of_acts_trivially h (a := 4) (b' := 5) (c' := 6) (by omega) (by omega)
    (by omega) huT huQ ?_
  refine c.commutator_of_correction h hBR (a := 4) (n := 6) (by omega) (by omega)
    (c.Vn_six_comm h hm10) hZa huV huT.1 fun w hw => ?_
  have hwT : w ∈ stab (p (m - 1)) ⊓ stab (p (m - 2)) := hQT2 (hA3 hw)
  obtain ⟨e₁, he₁A, hw₁⟩ : ∃ e₁ ∈ Vn V 4 (p 0), w * e₁⁻¹ ∈ ballStab 1 (p (m - 1)) := by
    by_cases hwQ : w ∈ ballStab 1 (p (m - 1))
    · exact ⟨1, one_mem _, by simpa using hwQ⟩
    · exact ⟨g₁, hg₁A, h.mul_inv_mem_ballStab_one hadj2 hwT hg₁T hwQ hg₁Q⟩
  obtain ⟨e₂, he₂W, hw₂⟩ : ∃ e₂ ∈ Vn V 2 (p 0), w * e₁⁻¹ * e₂⁻¹ ∈ ballStab 1 (p m) := by
    by_cases hwQ : w * e₁⁻¹ ∈ ballStab 1 (p m)
    · exact ⟨1, one_mem _, by simpa using hwQ⟩
    · exact ⟨g₀, hg₀W, h.mul_inv_mem_ballStab_one hadj (hQT hw₁) hg₀T hwQ hg₀Q⟩
  refine ⟨e₂ * e₁, (Vn V 4 (p 0)).mul_mem (Vn_mono (by omega) (p 0) he₂W) he₁A, ?_⟩
  have e : w * (e₂ * e₁)⁻¹ = w * e₁⁻¹ * e₂⁻¹ := by group
  rw [e]
  exact hw₂

end TypeIConfig

end GoldAmL3

end F6

end CFSG.Quasithin
