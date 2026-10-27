module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3XLadder
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3UExt
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3UF30

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

theorem Vn_two_comm (h : GoldHyp3 A B z V) :
    Vn V 2 (p 0) ≤ Subgroup.centralizer (Vn V 2 (p 0) : Set D) :=
  h.Vn_le_centralizer_Vn c.critDist_eq (n := 2) (n' := 2)
    (by rw [CosetGeom.dist_self]; have := c.six_le; omega)

omit [Finite D] in
theorem Zv_one_le_Vn (h : GoldHyp3 A B z V) : Zv z (p 1) ≤ Vn V 2 (p 0) :=
  (h.Zv_le_Vv (c.adj (Nat.zero_le _)) c.vtype_zero).trans
    (Vv_le_Vn c.vtype_zero (by rw [CosetGeom.dist_self]; exact Nat.zero_le _))

theorem twin (h : GoldHyp3 A B z V) (hBR : ¬ Vn V 2 (p 0) ≤ ballStab 1 (p m)) :
    Zv z (p 1) = Zv z (p (m - 1)) := by
  have hm6 := c.six_le
  obtain ⟨k, hk⟩ := c.even
  have hmt : vtype (p m) = false := c.vtype_even (by omega) c.even
  have hv1 : vtype (p 1) = true := c.vtype_odd (by omega) odd_one
  have hvm1 : vtype (p (m - 1)) = true := c.vtype_odd (by omega) ⟨k - 1, by omega⟩
  obtain ⟨g₀, hg₀W, hg₀Q⟩ := IsConcreteLE.not_le_iff_exists.1 hBR
  have hg₀1 : g₀ ∈ ballStab 1 (p (m - 1)) := c.Vn_two_le hg₀W
  have hg₀m : g₀ ∈ stab (p m) := ballStab_le_stab_of_dist_le (n := 1)
    (dist_eq_one_iff_adj.mpr (c.adj_pred (i := m) (by omega) (by omega)).symm).le hg₀1
  obtain ⟨c', hc'Z, hc'1⟩ := h.exists_ne_one_mem_Zv hv1
  have hc'V : c' ∈ Vv V (p m) := c.Zv_one_le h hc'Z
  have hcomm : g₀ * c' * g₀⁻¹ = c' :=
    mul_inv_eq_iff_eq_mul.mpr
      (Subgroup.mem_centralizer_iff.mp (c.Vn_two_comm h hg₀W) c' (c.Zv_one_le_Vn h hc'Z)).symm
  obtain ⟨t, ht, hct⟩ := h.exists_adj_mem_Zv hmt hc'V hc'1
  by_cases htm : t = p (m - 1)
  · subst htm
    exact eq_of_card_two_of_mem (h.card_Zv hv1) (h.card_Zv hvm1) hc'Z hct hc'1
  · exfalso
    have htt : vtype t = true := vtype_eq_true_of_adj ht hmt
    lift g₀ to ↥(A ⊔ B) using stab_le _ hg₀m with g'
    have hgm : g' • p m = p m := smul_eq_of_mem_stab hg₀m
    have hadj' : (graph (A ⊔ B) A B).Adj (p m) (g' • t) := by
      have := (smul_adj g').mpr ht
      rwa [hgm] at this
    have hc'' : c' ∈ Zv z (g' • t) := by
      rw [Zv_smul h.normalizes_zpowers]
      have := mul_mem_conjSub (g := (g' : D)) hct
      rwa [hcomm] at this
    have hZZ : Zv z (g' • t) = Zv z t :=
      eq_of_card_two_of_mem (h.card_Zv (by rwa [vtype_smul])) (h.card_Zv htt) hc'' hct hc'1
    have heq : g' • t = t := h.eq_of_Zv_eq hmt hadj' ht hZZ
    exact hg₀Q (h.mem_ballStab_one_of_fix_two_A hmt
      (c.adj_pred (i := m) (by omega) (by omega)) ht (fun e => htm e.symm) hg₀m
      (ballStab_le_stab 1 _ hg₀1) (mem_stab_of_smul_eq heq))

omit [Finite D] in
theorem exists_s (hBR : ¬ Vn V 2 (p 0) ≤ ballStab 1 (p m)) :
    ∃ s, (graph (A ⊔ B) A B).Adj (p 0) s ∧ ¬ Vv V s ≤ ballStab 1 (p m) := by
  by_contra hcon
  push Not at hcon
  refine hBR (Vn_le_iff.mpr fun l hl hd => ?_)
  obtain ⟨v, hv, hlv⟩ := c.exists_adj_Vv_le hl hd
  exact hlv.trans (hcon v hv)

omit [Finite D] in
theorem Vv_adj_le_Vn {s : CosetGeom (A ⊔ B) A B} (hs : (graph (A ⊔ B) A B).Adj (p 0) s) :
    Vv V s ≤ Vn V 2 (p 0) := by
  have hvs : vtype s = true := vtype_eq_true_of_adj hs c.vtype_zero
  refine (Vv_B_le_iff hvs).mpr fun l hl => Vv_le_Vn (vtype_eq_false_of_adj hl hvs) ?_
  have h1 := CosetGeom.dist_triangle (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) rfl (p 0) s l
  have h2 : CosetGeom.dist (p 0) s = 1 := dist_eq_one_iff_adj.mpr hs
  have h3 : CosetGeom.dist s l = 1 := dist_eq_one_iff_adj.mpr hl
  omega

theorem crit_s (h : GoldHyp3 A B z V) (hBR : ¬ Vn V 2 (p 0) ≤ ballStab 1 (p m))
    {s : CosetGeom (A ⊔ B) A B} (hs : (graph (A ⊔ B) A B).Adj (p 0) s)
    (hsQ : ¬ Vv V s ≤ ballStab 1 (p m)) : ¬ Vv V (p m) ≤ ballStab 1 s := by
  intro hVs
  have hm6 := c.six_le
  obtain ⟨k, hk⟩ := c.even
  have hmt : vtype (p m) = false := c.vtype_even (by omega) c.even
  have hv1 : vtype (p 1) = true := c.vtype_odd (by omega) odd_one
  have hvm1 : vtype (p (m - 1)) = true := c.vtype_odd (by omega) ⟨k - 1, by omega⟩
  have hvs : vtype s = true := vtype_eq_true_of_adj hs c.vtype_zero
  obtain ⟨y, hyV, hyQ⟩ := IsConcreteLE.not_le_iff_exists.1 hsQ
  have hy1 : y ∈ ballStab 1 (p (m - 1)) := c.Vn_two_le (c.Vv_adj_le_Vn hs hyV)
  have hadj : (graph (A ⊔ B) A B).Adj (p m) (p (m - 1)) :=
    c.adj_pred (i := m) (by omega) (by omega)
  have hym : y ∈ stab (p m) :=
    ballStab_le_stab_of_dist_le (n := 1) (dist_eq_one_iff_adj.mpr hadj.symm).le hy1
  have hyc : y ∈ stab (p m) ⊓ stab (p (m - 1)) := ⟨hym, ballStab_le_stab 1 _ hy1⟩
  obtain ⟨v', hv'V, hv'ne⟩ : ∃ v' ∈ Vv V (p m), y * v' * y⁻¹ ≠ v' := by
    by_contra hcon
    push Not at hcon
    exact hyQ (h.mem_ballStab_one_of_centralizes hmt hym hcon)
  have h1 : y * v' * y⁻¹ * v'⁻¹ ∈ Zv z (p (m - 1)) := h.commutator_mem_Zv hadj hmt hyc hv'V
  have h2 : v' * y * v'⁻¹ * y⁻¹ ∈ Zv z s :=
    h.commutator_mem_Zv_of_mem_ballStab_one hvs (hVs hv'V) hyV
  have hne1 : y * v' * y⁻¹ * v'⁻¹ ≠ 1 := fun e => hv'ne (mul_inv_eq_one.mp e)
  have e : v' * y * v'⁻¹ * y⁻¹ = (y * v' * y⁻¹ * v'⁻¹)⁻¹ := by group
  have h3 : y * v' * y⁻¹ * v'⁻¹ ∈ Zv z s := by
    have := (Zv z s).inv_mem h2
    rwa [e, inv_inv] at this
  have hZ : Zv z s = Zv z (p (m - 1)) :=
    eq_of_card_two_of_mem (h.card_Zv hvs) (h.card_Zv hvm1) h3 h1 hne1
  have hss : s = p 1 := h.eq_of_Zv_eq c.vtype_zero hs (c.adj (Nat.zero_le _))
    (hZ.trans (c.twin h hBR).symm)
  apply hsQ
  rw [hss]
  exact h.VvB_le_ballStab_one_of_dist c.critDist_eq hv1
    (by rw [c.geo 1 m (by omega) (by omega)]; omega)

theorem cap_s (h : GoldHyp3 A B z V) (hBR : ¬ Vn V 2 (p 0) ≤ ballStab 1 (p m))
    {s : CosetGeom (A ⊔ B) A B} (hs : (graph (A ⊔ B) A B).Adj (p 0) s)
    (hsQ : ¬ Vv V s ≤ ballStab 1 (p m)) {y : D} (hyV : y ∈ Vv V (p m))
    (hyQ : y ∈ ballStab 1 s) : y ∈ Zv z (p (m - 1)) := by
  have hm6 := c.six_le
  have hmt : vtype (p m) = false := c.vtype_even (by omega) c.even
  have hcrit := c.crit_s h hBR hs hsQ
  obtain ⟨q, hq0, hq1, hqs, hqe⟩ : ∃ q : ℕ → CosetGeom (A ⊔ B) A B, q 0 = p m ∧
      q 1 = p (m - 1) ∧ q (m + 1) = s ∧ ∀ i, i ≤ m → q i = p (m - i) :=
    ⟨fun i => if i ≤ m then p (m - i) else s, by simp, by simp [show 1 ≤ m by omega], by simp,
      fun i hi => by simp [hi]⟩
  have hgeo : IsGeo q (m + 1) := by
    refine isGeo_of_adj_of_dist rfl (fun i hi => ?_) ?_
    · by_cases him : i < m
      · rw [hqe i him.le, hqe (i + 1) him]
        have := c.adj_pred (i := m - i) (by omega) (by omega)
        rwa [show m - i - 1 = m - (i + 1) by omega] at this
      · rw [show i = m by omega, hqe m le_rfl, hqs, Nat.sub_self]
        exact hs
    · by_contra hlt
      rw [hq0, hqs] at hlt
      exact hcrit (h.Vv_le_ballStab_one_of_dist c.critDist_eq hmt (by omega))
  have := h.mem_Zv_of_mem_Vv_of_mem_ballStab c.critDist_eq hgeo (by rw [hq0]; exact hmt)
    (by rw [hq0, hqs]; exact hcrit) (by rw [hq0]; exact hyV) (by rw [hqs]; exact hyQ)
  rwa [hq1] at this

theorem Vn_inf_Vv_le (h : GoldHyp3 A B z V) (hBR : ¬ Vn V 2 (p 0) ≤ ballStab 1 (p m)) {n : ℕ}
    (hn : n + 1 ≤ m) {y : D} (hy : y ∈ Vn V n (p 0)) (hyV : y ∈ Vv V (p m)) :
    y ∈ Zv z (p (m - 1)) := by
  obtain ⟨s, hs, hsQ⟩ := c.exists_s hBR
  have hd : CosetGeom.dist (p 0) s = 1 := dist_eq_one_iff_adj.mpr hs
  exact c.cap_s h hBR hs hsQ hyV (h.Vn_le_ballStab_one c.critDist_eq (by omega) hy)

end TypeIConfig

end GoldAmL3

end F6

end CFSG.Quasithin
