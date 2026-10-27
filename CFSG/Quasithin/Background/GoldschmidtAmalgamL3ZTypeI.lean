module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3ZRank
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3WBase

public section

namespace CFSG.Quasithin

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

structure TypeIConfigG {D : Type*} [Group D] {A B : Subgroup D} (V : Subgroup D) (m : ℕ)
    (p : ℕ → CosetGeom (A ⊔ B) A B) : Prop where
  crit_eq : critDist (A ⊔ B) A B V = m + 1
  six_le : 6 ≤ m
  even : Even m
  start : p 0 = γ₀ (A ⊔ B) A B
  geo : IsGeo p (m + 1)
  crit : ¬ V ≤ ballStab 1 (p (m + 1))
  good : ∀ v, (graph (A ⊔ B) A B).Adj (p 0) v → Vv V v ≤ ballStab 1 (p (m - 1))
  typeI : Vv V (p (m + 1)) ≤ ballStab 1 (p 1)

namespace TypeIConfigG

variable {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (c : TypeIConfigG V m p)

include c

theorem vtype_zero : vtype (p 0) = false := by
  rw [c.start]
  exact vtype_γ₀

theorem vtype_even {i : ℕ} (hi : i ≤ m + 1) (he : Even i) : vtype (p i) = false :=
  c.geo.vtype_false_of_even_start rfl c.vtype_zero hi he

theorem vtype_odd {i : ℕ} (hi : i ≤ m + 1) (ho : Odd i) : vtype (p i) = true :=
  c.geo.vtype_true_of_odd_start rfl c.vtype_zero hi ho

theorem adj {i : ℕ} (hi : i ≤ m) : (graph (A ⊔ B) A B).Adj (p i) (p (i + 1)) :=
  c.geo.adj (by omega)

theorem Vv_zero (h : GoldHyp3 A B z V) : Vv V (p 0) = V := by
  rw [c.start]
  exact Vv_γ₀ h.natural.reduced.2.1

theorem crit' (h : GoldHyp3 A B z V) : ¬ Vv V (p 0) ≤ ballStab 1 (p (m + 1)) := by
  rw [c.Vv_zero h]
  exact c.crit

theorem exists_adj_Vv_le {l : CosetGeom (A ⊔ B) A B} (hl : vtype l = false)
    (hd : CosetGeom.dist (p 0) l ≤ 2) :
    ∃ v, (graph (A ⊔ B) A B).Adj (p 0) v ∧ Vv V l ≤ Vv V v := by
  by_cases hl0 : l = p 0
  · obtain ⟨v, hv⟩ := exists_adj (p 0)
    exact ⟨v, hv, hl0 ▸ Vv_le_Vv_of_adj hv c.vtype_zero⟩
  · have heven : Even (CosetGeom.dist (p 0) l) :=
      (vtype_eq_iff_even_dist rfl (p 0) l).mp (by rw [c.vtype_zero, hl])
    have hpos : CosetGeom.dist (p 0) l ≠ 0 := fun e => hl0 ((dist_eq_zero_iff rfl).mp e).symm
    have h2 : CosetGeom.dist (p 0) l = 1 + 1 := by
      obtain ⟨k, hk⟩ := heven
      omega
    obtain ⟨β, hβ, hβd⟩ := exists_adj_dist_eq rfl h2
    exact ⟨β, dist_eq_one_iff_adj.mp hβd, Vv_le_Vv_of_adj hβ hl⟩

theorem Vn_two_le : Vn V 2 (p 0) ≤ ballStab 1 (p (m - 1)) := by
  refine Vn_le_iff.mpr fun l hl hd => ?_
  obtain ⟨v, hv, hlv⟩ := c.exists_adj_Vv_le hl hd
  exact hlv.trans (c.good v hv)

variable [Finite D] (h : GoldHyp3 A B z V)

include h

theorem exists_u :
    ∃ u : D, u ∈ Vv V (p (m + 1)) ∧ u ∈ stab (p 0) ⊓ stab (p 1) ∧ u ∉ ballStab 1 (p 0) := by
  have hp := c.geo
  have hb := c.crit_eq
  have hbt : vtype (p (m + 1)) = true := c.vtype_odd le_rfl c.even.add_one
  obtain ⟨x₀, hx₀V, hx₀Q⟩ := IsConcreteLE.not_le_iff_exists.1 (c.crit' h)
  have hx₀b : x₀ ∈ stab (p (m + 1)) :=
    h.Vv_le_stab_A hb c.vtype_zero (by rw [hp 0 (m + 1) (Nat.zero_le _) le_rfl]; omega) hx₀V
  obtain ⟨u, hu, hnc⟩ : ∃ u ∈ Vv V (p (m + 1)), x₀ * u * x₀⁻¹ * u⁻¹ ∉ Zv z (p (m + 1)) := by
    by_contra hcon
    push Not at hcon
    exact hx₀Q (h.mem_ballStab_one_of_commutator hbt hx₀b hcon)
  have huI : u ∈ ballStab 1 (p 1) := c.typeI hu
  refine ⟨u, hu, ⟨?_, ballStab_le_stab 1 _ huI⟩, fun huQ => hnc ?_⟩
  · refine ballStab_le_stab_of_dist_le (n := 1) ?_ huI
    have := hp 0 1 (by omega) (by omega)
    rw [CosetGeom.dist_comm]
    omega
  · have e1 := h.ballStab_one_le_centralizer_Vv c.vtype_zero huQ hx₀V
    have e2 : u * x₀ = x₀ * u := mul_inv_eq_iff_eq_mul.mp e1
    have e3 : x₀ * u * x₀⁻¹ * u⁻¹ = 1 := by
      rw [← e2]
      group
    rw [e3]
    exact one_mem _

theorem false_of_typeI (hU : Nat.card (conjClosure V B) = 16)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false →
      (graph (A ⊔ B) A B).Adj u β → (graph (A ⊔ B) A B).Adj u β' → β ≠ β' →
        Vv V β ⊓ Vv V β' ≤ Vv V u) : False := by
  have hm := c.six_le
  have hv0 : vtype (p 0) = false := c.vtype_zero
  have hvm : vtype (p m) = false := c.vtype_even (by omega) c.even
  have hvb : vtype (p (m + 1)) = true := c.vtype_odd le_rfl c.even.add_one
  have h01 : (graph (A ⊔ B) A B).Adj (p 0) (p 1) := c.adj (i := 0) (by omega)
  have hmm : (graph (A ⊔ B) A B).Adj (p m) (p (m + 1)) := c.adj (i := m) le_rfl
  have hdm : CosetGeom.dist (p m) (p (m + 1)) ≤ 1 := (CosetGeom.dist_eq_one_iff_adj.mpr hmm).le
  have hU' : Nat.card (Vv V (p (m + 1))) = 16 := h.card_Vv_B_of_card hU hvb
  obtain ⟨y, hyU, hyT, hyQ⟩ := c.exists_u h
  obtain ⟨v, hv, hvn⟩ : ∃ v ∈ Vv V (p 0), y * v * y⁻¹ ≠ v := by
    by_contra hcon
    push Not at hcon
    exact hyQ (h.mem_ballStab_one_of_centralizes hv0 hyT.1 hcon)
  have hζ1 : y * v * y⁻¹ * v⁻¹ ≠ 1 := fun e => hvn (mul_inv_eq_one.mp e)
  have hζZ : y * v * y⁻¹ * v⁻¹ ∈ Zv z (p 1) := h.commutator_mem_Zv h01 hv0 hyT hv
  have hζV : y * v * y⁻¹ * v⁻¹ ∈ Vv V (p 0) := h.Zv_le_Vv h01 hv0 hζZ
  have hvQ : v ∈ ballStab 1 (p m) := by
    refine h.Vv_le_ballStab_one_of_dist c.crit_eq hv0 ?_ hv
    have := c.geo 0 m (Nat.zero_le _) (by omega)
    omega
  have hvT : v ∈ stab (p m) ⊓ stab (p (m + 1)) :=
    ⟨ballStab_le_stab 1 _ hvQ, ballStab_le_stab_of_dist_le (n := 1) hdm hvQ⟩
  have hΘ : y * v * y⁻¹ * v⁻¹ ∈ Theta z V (p m) (p (m + 1)) := by
    have e : y * v * y⁻¹ * v⁻¹ = (v * y * v⁻¹ * y⁻¹)⁻¹ := by group
    rw [e]
    exact (Theta z V (p m) (p (m + 1))).inv_mem (comm_mem_Theta hvT hyU z)
  have hWab : Vn V 2 (p 0) ≤ Subgroup.centralizer (Vn V 2 (p 0) : Set D) :=
    h.Vn_le_centralizer_Vn c.crit_eq (by rw [CosetGeom.dist_self]; omega)
  generalize y * v * y⁻¹ * v⁻¹ = ζ at hζ1 hζZ hζV hΘ
  by_cases hnb : Vn V 2 (p 0) ≤ ballStab 1 (p m)
  ·
    have hcomm : ∀ w ∈ Vn V 2 (p 0), w * y * w⁻¹ * y⁻¹ ∈ Theta z V (p m) (p (m + 1)) :=
      fun w hw => comm_mem_Theta ⟨ballStab_le_stab 1 _ (hnb hw),
        ballStab_le_stab_of_dist_le (n := 1) hdm (hnb hw)⟩ hyU z
    exact h.false_of_comm_mem_card_le hU hI1 hv0 h01 hWab hyT hyQ (h.card_Theta_le_four hvm hmm)
      hΘ hζV hζ1 hcomm
  · obtain ⟨g₀, hg₀W, hg₀n⟩ := IsConcreteLE.not_le_iff_exists.mp hnb
    have hg₀a := c.Vn_two_le hg₀W
    have hadjm : (graph (A ⊔ B) A B).Adj (p (m - 1)) (p m) := by
      have := c.adj (i := m - 1) (by omega)
      rwa [show m - 1 + 1 = m by omega] at this
    have hdm1 : CosetGeom.dist (p (m - 1)) (p m) ≤ 1 :=
      (CosetGeom.dist_eq_one_iff_adj.mpr hadjm).le
    have hg₀s1 : g₀ ∈ stab (p (m - 1)) := ballStab_le_stab 1 _ hg₀a
    have hg₀s : g₀ ∈ stab (p m) := ballStab_le_stab_of_dist_le (n := 1) hdm1 hg₀a
    have hne : p (m - 1) ≠ p (m + 1) := c.geo.ne (by omega) le_rfl
    obtain ⟨b₂, hb₂, hb₂1, hb₂2⟩ := h.exists_third (w := p m) (u := p (m - 1)) (v := p (m + 1))
      hne
    have hb₂t : vtype b₂ = true := vtype_eq_true_of_adj hb₂ hvm
    have hswap := h.smul_eq_of_not_mem_ballStab hadjm.symm hmm hb₂ hne.symm hb₂1 (Ne.symm hb₂2)
      hg₀s hg₀s1 hg₀n
    set g : ↥(A ⊔ B) := ⟨g₀, stab_le (p m) hg₀s⟩ with hg
    have hgm : g • p m = p m := smul_eq_of_mem_stab hg₀s
    have hswap' : g • p (m + 1) = b₂ := hswap
    have hΘ' : Theta z V (p m) b₂ = conjSub g₀ (Theta z V (p m) (p (m + 1))) := by
      have := h.Theta_smul g (p m) (p (m + 1))
      rwa [hgm, hswap'] at this
    have hζW : ζ ∈ Vn V 2 (p 0) :=
      Vv_le_Vn hv0 (by rw [CosetGeom.dist_self]; omega) hζV
    have hfix : g₀ * ζ * g₀⁻¹ = ζ := by
      have := Subgroup.mem_centralizer_iff.mp (hWab hg₀W) _ hζW
      calc g₀ * ζ * g₀⁻¹ = (ζ * g₀) * g₀⁻¹ := by rw [this]
        _ = ζ := by group
    have hΘ2 : ζ ∈ Theta z V (p m) b₂ := by
      rw [hΘ']
      have := mul_mem_conjSub (g := g₀) hΘ
      rwa [hfix] at this
    have hζI : ζ ∈ Vv V (p m) :=
      hI1 (p m) (p (m + 1)) b₂ hvm hmm hb₂ (Ne.symm hb₂2)
        ⟨h.Theta_le_Vv hvm hmm hΘ, h.Theta_le_Vv hvm hb₂ hΘ2⟩
    have hζZ1 : ζ ∈ Zv z (p (m + 1)) := by
      rw [← h.Theta_inf_Vv hvm hmm hU']
      exact ⟨hΘ, hζI⟩
    have hζZ2 : ζ ∈ Zv z b₂ := by
      have e := Zv_smul h.normalizes_zpowers g (p (m + 1))
      rw [hswap'] at e
      rw [e]
      have := mul_mem_conjSub (g := g₀) hζZ1
      rwa [hfix] at this
    have hzz := h.Zv_eq_of_mem hvb hb₂t hζZ1 hζZ2 hζ1
    exact hb₂2 (h.eq_of_Zv_eq hvm hmm hb₂ hzz).symm

end TypeIConfigG

end GoldAmL3

end F6

end CFSG.Quasithin
