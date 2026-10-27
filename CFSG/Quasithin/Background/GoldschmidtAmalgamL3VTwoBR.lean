module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VTwoBase
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3XBasic
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3UExt
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3XFix

public section

namespace CFSG.Quasithin

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem coincidence_odd_I_gen (hU : Nat.card (conjClosure V B) = 8) {m : ℕ}
    (hb : critDist (A ⊔ B) A B V = m + 1) (hm : 2 ≤ m)
    {q : ℕ → CosetGeom (A ⊔ B) A B} (hq : IsGeo q (m + 1)) (hq0 : vtype (q 0) = false)
    (hcrit : ¬ Vv V (q 0) ≤ ballStab 1 (q (m + 1))) (hodd : vtype (q (m + 1)) = true)
    (hI : Vv V (q (m + 1)) ≤ ballStab 1 (q 1)) :
    ∃ c : D, c ≠ 1 ∧ c ∈ Zv z (q 1) ∧ c ∈ Vv V (q m) := by
  have h01 : (graph (A ⊔ B) A B).Adj (q 0) (q 1) := hq.adj (i := 0) (by omega)
  have hmm : (graph (A ⊔ B) A B).Adj (q m) (q (m + 1)) := hq.adj (i := m) (by omega)
  have hvm : vtype (q m) = false := vtype_eq_false_of_adj hmm.symm hodd
  obtain ⟨x, hx0, hxn⟩ := IsConcreteLE.not_le_iff_exists.1 hcrit
  have hd1 : CosetGeom.dist (q 0) (q (m + 1)) ≤ m + 1 := by
    have := hq 0 (m + 1) (by omega) le_rfl
    omega
  have hd2 : CosetGeom.dist (q 0) (q m) ≤ m + 1 := by
    have := hq 0 m (by omega) (by omega)
    omega
  have hxa : x ∈ stab (q (m + 1)) := h.Vv_le_stab_A hb hq0 hd1 hx0
  have hxb : x ∈ stab (q m) := h.Vv_le_stab_A hb hq0 hd2 hx0
  have hnc : ¬ ∀ w ∈ Vv V (q (m + 1)), x * w * x⁻¹ * w⁻¹ ∈ Zv z (q (m + 1)) := fun hall =>
    hxn (h.mem_ballStab_one_of_commutator hodd hxa hall)
  push Not at hnc
  obtain ⟨w, hw, hxw⟩ := hnc
  have hc1 : x * w * x⁻¹ * w⁻¹ ≠ 1 := fun e => hxw (by rw [e]; exact (Zv z _).one_mem)
  have hcm : x * w * x⁻¹ * w⁻¹ ∈ Vv V (q m) := h.commutator_mem_Vv hU hmm hvm ⟨hxb, hxa⟩ hw
  have hwI : w ∈ ballStab 1 (q 1) := hI hw
  have hwb : w ∈ stab (q 1) := ballStab_le_stab 1 (q 1) hwI
  have hwa : w ∈ stab (q 0) := by
    refine ballStab_le_stab_of_dist_le (n := 1) ?_ hwI
    rw [CosetGeom.dist_comm]
    have := hq 0 1 (by omega) (by omega)
    omega
  have hc1' : w * x * w⁻¹ * x⁻¹ ∈ Zv z (q 1) := h.commutator_mem_Zv h01 hq0 ⟨hwa, hwb⟩ hx0
  refine ⟨x * w * x⁻¹ * w⁻¹, hc1, ?_, hcm⟩
  have e : x * w * x⁻¹ * w⁻¹ = (w * x * w⁻¹ * x⁻¹)⁻¹ := by group
  rw [e]
  exact (Zv z (q 1)).inv_mem hc1'

end GoldHyp3

namespace TypeIIConfig

variable {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (c : TypeIIConfig V m p)

include c

omit [Finite D] in
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

omit [Finite D] in
theorem Vn_two_le (hgood : ∀ v, (graph (A ⊔ B) A B).Adj (p 0) v →
    Vv V v ≤ ballStab 1 (p (m - 1))) : Vn V 2 (p 0) ≤ ballStab 1 (p (m - 1)) := by
  refine Vn_le_iff.mpr fun l hl hd => ?_
  obtain ⟨v, hv, hlv⟩ := c.exists_adj_Vv_le hl hd
  exact hlv.trans (hgood v hv)

theorem false_of_mem_inf (h : GoldHyp3 A B z V) {x : D} (hx0 : x ∈ Vv V (p 0))
    (hx2 : x ∈ Vv V (p 2)) (hxZ : x ∉ Zv z (p 1)) : False := by
  have hm := c.eight_le
  have hv0 := c.vtype_zero
  have hv1 : vtype (p 1) = true := c.vtype_odd (by omega) odd_one
  have hv2 : vtype (p 2) = false := c.vtype_even (by omega) (by decide)
  have h01 : (graph (A ⊔ B) A B).Adj (p 0) (p 1) := c.adj (Nat.zero_le _)
  have h12 : (graph (A ⊔ B) A B).Adj (p 1) (p 2) := c.adj (i := 1) (by omega)
  have hZ0 : Zv z (p 1) ≤ Vv V (p 0) := h.Zv_le_Vv h01 hv0
  have hZ2 : Zv z (p 1) ≤ Vv V (p 2) := h.Zv_le_Vv h12.symm hv2
  have h02 : Vv V (p 0) ≤ Vv V (p 2) :=
    le_of_card_four (h.card_Vv_A hv0) (h.card_Zv hv1) hZ0 hZ2 hx0 hx2 hxZ
  have h20 : Vv V (p 2) ≤ Vv V (p 0) :=
    le_of_card_four (h.card_Vv_A hv2) (h.card_Zv hv1) hZ2 hZ0 hx2 hx0 hxZ
  exact c.geo.ne (i := 0) (j := 2) (by omega) (by omega)
    (h.eq_of_Vv_eq hv1 h01.symm h12 (le_antisymm h02 h20))

theorem twin (h : GoldHyp3 A B z V) (hgood : ∀ v, (graph (A ⊔ B) A B).Adj (p 0) v →
    Vv V v ≤ ballStab 1 (p (m - 1))) (hBR : ¬ Vn V 2 (p 0) ≤ ballStab 1 (p m)) {x : D}
    (hx1 : x ≠ 1) (hx2 : x ∈ Vv V (p 2)) (hxm : x ∈ Vv V (p m)) : x ∈ Zv z (p (m - 1)) := by
  have hm := c.eight_le
  obtain ⟨k, hk⟩ := c.even
  have hmt : vtype (p m) = false := c.vtype_even (by omega) c.even
  have hv2 : vtype (p 2) = false := c.vtype_even (by omega) (by decide)
  have hvm1 : vtype (p (m - 1)) = true := c.vtype_odd (by omega) ⟨k - 1, by omega⟩
  have hadj : (graph (A ⊔ B) A B).Adj (p m) (p (m - 1)) := c.adj_pred (i := m) (by omega) (by omega)
  obtain ⟨g₀, hg₀W, hg₀Q⟩ := IsConcreteLE.not_le_iff_exists.1 hBR
  have hg₀1 : g₀ ∈ ballStab 1 (p (m - 1)) := c.Vn_two_le hgood hg₀W
  have hg₀m : g₀ ∈ stab (p m) :=
    ballStab_le_stab_of_dist_le (n := 1) (dist_eq_one_iff_adj.mpr hadj.symm).le hg₀1
  have hxW : x ∈ Vn V 2 (p 0) :=
    (Vv_le_Vn hv2 (by have := c.dist_eq (i := 0) (j := 2) (by omega) (by omega); omega) :
      Vv V (p 2) ≤ Vn V 2 (p 0)) hx2
  have hWab : Vn V 2 (p 0) ≤ Subgroup.centralizer (Vn V 2 (p 0) : Set D) :=
    h.Vn_le_centralizer_Vn c.critDist_eq (n := 2) (n' := 2) (by rw [CosetGeom.dist_self]; omega)
  have hcomm : g₀ * x * g₀⁻¹ = x :=
    mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp (hWab hg₀W) x hxW).symm
  obtain ⟨t, ht, hxt⟩ := h.exists_adj_mem_Zv hmt hxm hx1
  by_cases htm : t = p (m - 1)
  · subst htm
    exact hxt
  · exfalso
    have htt : vtype t = true := vtype_eq_true_of_adj ht hmt
    lift g₀ to ↥(A ⊔ B) using stab_le _ hg₀m with g'
    have hgm : g' • p m = p m := smul_eq_of_mem_stab hg₀m
    have hadj' : (graph (A ⊔ B) A B).Adj (p m) (g' • t) := by
      have := (smul_adj g').mpr ht
      rwa [hgm] at this
    have hx'' : x ∈ Zv z (g' • t) := by
      rw [Zv_smul h.normalizes_zpowers]
      have := mul_mem_conjSub (g := (g' : D)) hxt
      rwa [hcomm] at this
    have hZZ : Zv z (g' • t) = Zv z t :=
      eq_of_card_two_of_mem (h.card_Zv (by rwa [vtype_smul])) (h.card_Zv htt) hx'' hxt hx1
    have heq : g' • t = t := h.eq_of_Zv_eq hmt hadj' ht hZZ
    exact hg₀Q (h.mem_ballStab_one_of_fix_two_A hmt hadj ht (fun e => htm e.symm) hg₀m
      (ballStab_le_stab 1 _ hg₀1) (mem_stab_of_smul_eq heq))

omit [Finite D] in
theorem exists_s (hBR : ¬ Vn V 2 (p 0) ≤ ballStab 1 (p m)) :
    ∃ s, (graph (A ⊔ B) A B).Adj (p 0) s ∧ ¬ Vv V s ≤ ballStab 1 (p m) := by
  by_contra hcon
  push Not at hcon
  refine hBR (Vn_le_iff.mpr fun l hl hd => ?_)
  obtain ⟨v, hv, hlv⟩ := c.exists_adj_Vv_le hl hd
  exact hlv.trans (hcon v hv)

theorem crit_s (h : GoldHyp3 A B z V) (hgood : ∀ v, (graph (A ⊔ B) A B).Adj (p 0) v →
    Vv V v ≤ ballStab 1 (p (m - 1))) {x : D} (hxt : x ∈ Zv z (p (m - 1)))
    (hx2 : x ∈ Vv V (p 2)) (hxZ : x ∉ Zv z (p 1)) {s : CosetGeom (A ⊔ B) A B}
    (hs : (graph (A ⊔ B) A B).Adj (p 0) s) (hsQ : ¬ Vv V s ≤ ballStab 1 (p m)) :
    ¬ Vv V (p m) ≤ ballStab 1 s := by
  intro hVs
  have hm := c.eight_le
  obtain ⟨k, hk⟩ := c.even
  have hmt : vtype (p m) = false := c.vtype_even (by omega) c.even
  have hvm1 : vtype (p (m - 1)) = true := c.vtype_odd (by omega) ⟨k - 1, by omega⟩
  have hvs : vtype s = true := vtype_eq_true_of_adj hs c.vtype_zero
  obtain ⟨y, hyV, hyQ⟩ := IsConcreteLE.not_le_iff_exists.1 hsQ
  have hy1 : y ∈ ballStab 1 (p (m - 1)) := hgood s hs hyV
  have hadj : (graph (A ⊔ B) A B).Adj (p m) (p (m - 1)) := c.adj_pred (i := m) (by omega) (by omega)
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
  have hx0 : x ∈ Vv V (p 0) := h.Zv_le_Vv hs c.vtype_zero (by rw [hZ]; exact hxt)
  exact c.false_of_mem_inf h hx0 hx2 hxZ

theorem false_of_BR (h : GoldHyp3 A B z V) (hgood : ∀ v, (graph (A ⊔ B) A B).Adj (p 0) v →
    Vv V v ≤ ballStab 1 (p (m - 1))) (hBR : ¬ Vn V 2 (p 0) ≤ ballStab 1 (p m)) : False := by
  have hm := c.eight_le
  obtain ⟨k, hk⟩ := c.even
  have hmt : vtype (p m) = false := c.vtype_even (by omega) c.even
  have hvm1 : vtype (p (m - 1)) = true := c.vtype_odd (by omega) ⟨k - 1, by omega⟩
  obtain ⟨x, hx1, hx2, hxm, hxZ⟩ := c.exists_c h
  have hxt : x ∈ Zv z (p (m - 1)) := c.twin h hgood hBR hx1 hx2 hxm
  obtain ⟨s, hs, hsQ⟩ := c.exists_s hBR
  have hvs : vtype s = true := vtype_eq_true_of_adj hs c.vtype_zero
  have hcrit : ¬ Vv V (p m) ≤ ballStab 1 s := c.crit_s h hgood hxt hx2 hxZ hs hsQ
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
      · obtain rfl : i = m := by omega
        rw [hqe i le_rfl, hqs, Nat.sub_self]
        exact hs
    · by_contra hlt
      rw [hq0, hqs] at hlt
      exact hcrit (h.Vv_le_ballStab_one_of_dist c.critDist_eq hmt (by omega))
  have hI : Vv V (q (m + 1)) ≤ ballStab 1 (q 1) := by
    rw [hqs, hq1]
    exact hgood s hs
  obtain ⟨c', hc'1, hc'Z, hc'V⟩ := h.coincidence_odd_I_gen c.card c.critDist_eq (by omega) hgeo
    (by rw [hq0]; exact hmt) (by rw [hq0, hqs]; exact hcrit) (by rw [hqs]; exact hvs) hI
  rw [hq1] at hc'Z
  rw [hqe m le_rfl, Nat.sub_self] at hc'V
  have hZV : Zv z (p (m - 1)) ≤ Vv V (p 0) :=
    le_of_card_two_of_mem (h.card_Zv hvm1) hc'Z hc'V hc'1
  exact c.false_of_mem_inf h (hZV hxt) hx2 hxZ

end TypeIIConfig

end GoldAmL3

end F6

end CFSG.Quasithin
