module

public import CFSG.Quasithin.Recognition.Stroth.MoufangCommutator

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair

open scoped Pointwise

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]

theorem aptRoot_eq_one_of_fix_adj_start {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    {g : D} {k : ℤ} (hg : g ∈ aptRoot D Γ n t k) (hn : 3 ≤ n)
    (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) {w : V}
    (hw : Γ.Adj (apt t k) w) (hw' : w ≠ apt t (k + 1)) (hgw : g • w = w) : g = 1 := by
  have hlast : aptPathRev ht.2 k n = apt t k := by
    rw [aptPathRev_apply ht.2 k le_rfl]
    rw [show k + (n : ℤ) - (n : ℤ) = k by ring]
  have hpen : aptPathRev ht.2 k (n - 1) = apt t (k + 1) := by
    rw [aptPathRev_apply ht.2 k (by omega)]
    rw [show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num]
    rw [show k + (n : ℤ) - ((n : ℤ) - 1) = k + 1 by ring]
  refine pathRootGroup_eq_one_of_fix hn hP hT (aptPathRev_noBack (by omega) ht k) ?_
    (by rwa [hlast]) (by rwa [hpen]) hgw
  rwa [← aptRoot_eq_pathRootGroupRev (by omega) ht k]

theorem aptRoot_ne_bot {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) (hM : MoufangCondition D Γ n) (k : ℤ) :
    aptRoot D Γ n t k ≠ ⊥ := by
  classical
  have hmem1 : apt t (k + (n : ℤ) - 1) ∈ Γ.neighborFinset (apt t (k + (n : ℤ))) := by
    rw [SimpleGraph.mem_neighborFinset]
    have h := (apt_adj ht (k + (n : ℤ) - 1)).symm
    rwa [show k + (n : ℤ) - 1 + 1 = k + (n : ℤ) by ring] at h
  have hdeg : 3 ≤ (Γ.neighborFinset (apt t (k + (n : ℤ)))).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hT _
  have hcard : 1 <
      ((Γ.neighborFinset (apt t (k + (n : ℤ)))).erase (apt t (k + (n : ℤ) - 1))).card := by
    rw [Finset.card_erase_of_mem hmem1]
    omega
  obtain ⟨y, hy, y', hy', hyne⟩ := Finset.one_lt_card.mp hcard
  rw [Finset.mem_erase] at hy hy'
  rw [SimpleGraph.mem_neighborFinset] at hy hy'
  obtain ⟨g, hg, hgy⟩ := aptRoot_exists_smul_of_adj ht hn hM (k := k) hy.2 hy'.2 hy.1 hy'.1
  intro hbot
  have hg1 : g = 1 := by
    have : g ∈ (⊥ : Subgroup D) := by rw [← hbot]; exact hg
    simpa using this
  exact hyne (by rw [← hgy, hg1, one_smul])

theorem aptRoot_prod_unique {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) {a b : ℤ} (hab : a ≤ b)
    (hbn : b < a + (n : ℤ)) {f g : ℤ → D}
    (hf : ∀ k ∈ intList a b, f k ∈ aptRoot D Γ n t k)
    (hg : ∀ k ∈ intList a b, g k ∈ aptRoot D Γ n t k)
    (heq : ((intList a b).map f).prod = ((intList a b).map g).prod) :
    ∀ k ∈ intList a b, f k = g k := by
  have key : ∀ k : ℕ, ∀ a b : ℤ, (b - a).toNat = k → a ≤ b → b < a + (n : ℤ) → ∀ f g : ℤ → D,
      (∀ k ∈ intList a b, f k ∈ aptRoot D Γ n t k) →
      (∀ k ∈ intList a b, g k ∈ aptRoot D Γ n t k) →
      ((intList a b).map f).prod = ((intList a b).map g).prod →
      ∀ k ∈ intList a b, f k = g k := by
    intro k
    induction k with
    | zero =>
      intro a b hk hab hbn f g hf hg heq i hi
      have hba : b = a := by
        have h0 : 0 ≤ b - a := by omega
        have h1 : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg h0
        rw [hk] at h1
        omega
      rw [hba] at heq hi
      rw [show intList a a = [a] by simp [intList]] at heq hi
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at heq
      rw [List.mem_singleton] at hi
      subst hi
      exact heq
    | succ k ih =>
      intro a b hk hab hbn f g hf hg heq i hi
      have hlt : a < b := by
        rcases lt_or_eq_of_le hab with h | h
        · exact h
        · exfalso
          have : (b - a).toNat = 0 := by rw [h]; simp
          omega
      have hsplit_f : ((intList a b).map f).prod = f a * ((intList (a + 1) b).map f).prod := by
        rw [intList_cons (le_of_lt hlt), List.map_cons, List.prod_cons]
      have hsplit_g : ((intList a b).map g).prod = g a * ((intList (a + 1) b).map g).prod := by
        rw [intList_cons (le_of_lt hlt), List.map_cons, List.prod_cons]
      have hafix : ∀ k : ℤ, a + 1 ≤ k → k ≤ b →
          aptRoot D Γ n t k ≤ fixingSubgroup D (Γ.neighborSet (apt t (a + (n : ℤ)))) := by
        intro j hj1 hj2
        exact aptRoot_le_star (t := t) ht (by omega) (by omega)
      have hfix_g : ((intList (a + 1) b).map g).prod ∈
          fixingSubgroup D (Γ.neighborSet (apt t (a + (n : ℤ)))) := by
        refine Subgroup.list_prod_mem _ ?_
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        rw [mem_intList_iff] at hj
        exact hafix j hj.1 hj.2 (hg j (by rw [mem_intList_iff]; omega))
      have hfix_f : ((intList (a + 1) b).map f).prod ∈
          fixingSubgroup D (Γ.neighborSet (apt t (a + (n : ℤ)))) := by
        refine Subgroup.list_prod_mem _ ?_
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        rw [mem_intList_iff] at hj
        exact hafix j hj.1 hj.2 (hf j (by rw [mem_intList_iff]; omega))
      have hx : (g a)⁻¹ * f a = ((intList (a + 1) b).map g).prod *
          (((intList (a + 1) b).map f).prod)⁻¹ := by
        have h := heq
        rw [hsplit_f, hsplit_g] at h
        calc (g a)⁻¹ * f a = (g a)⁻¹ * (f a * ((intList (a + 1) b).map f).prod) *
              ((intList (a + 1) b).map f).prod⁻¹ := by group
          _ = (g a)⁻¹ * (g a * ((intList (a + 1) b).map g).prod) *
              ((intList (a + 1) b).map f).prod⁻¹ := by rw [h]
          _ = ((intList (a + 1) b).map g).prod * (((intList (a + 1) b).map f).prod)⁻¹ := by group
      have hxfix : (g a)⁻¹ * f a ∈
          fixingSubgroup D (Γ.neighborSet (apt t (a + (n : ℤ)))) := by
        rw [hx]
        exact Subgroup.mul_mem _ hfix_g (Subgroup.inv_mem _ hfix_f)
      have hxa : (g a)⁻¹ * f a ∈ aptRoot D Γ n t a := by
        refine Subgroup.mul_mem _ (Subgroup.inv_mem _ (hg a ?_)) (hf a ?_)
        · rw [intList_cons (le_of_lt hlt)]; simp
        · rw [intList_cons (le_of_lt hlt)]; simp
      have hgw : ((g a)⁻¹ * f a) • apt t (a + (n : ℤ) + 1) = apt t (a + (n : ℤ) + 1) := by
        have h := (mem_fixingSubgroup_iff D).mp hxfix (apt t (a + (n : ℤ) + 1))
          (by rw [SimpleGraph.mem_neighborSet]; exact apt_adj ht (a + (n : ℤ)))
        simpa using h
      have hwne : apt t (a + (n : ℤ) + 1) ≠ apt t (a + (n : ℤ) - 1) := by
        have h := apt_ne_two (by omega : 2 ≤ n) ht (a + (n : ℤ) - 1)
        rw [show a + (n : ℤ) - 1 + 2 = a + (n : ℤ) + 1 by ring] at h
        exact fun hc => h hc.symm
      have hone : (g a)⁻¹ * f a = 1 :=
        aptRoot_eq_one_of_fix_adj ht hxa hn hP hT (apt_adj ht (a + (n : ℤ))) hwne hgw
      have hfa : f a = g a := by
        have h := congrArg (fun z => g a * z) hone
        simpa using h
      have hrf : ((intList (a + 1) b).map f).prod = ((intList (a + 1) b).map g).prod := by
        have h := heq
        rw [hsplit_f, hsplit_g, hfa] at h
        exact mul_left_cancel h
      have hk' : (b - (a + 1)).toNat = k := by
        have h1 : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
        have h2 : ((b - (a + 1)).toNat : ℤ) = b - (a + 1) := Int.toNat_of_nonneg (by omega)
        have h3 : ((b - a).toNat : ℤ) = (k : ℤ) + 1 := by rw [hk]; norm_num
        have : ((b - (a + 1)).toNat : ℤ) = ((k : ℕ) : ℤ) := by
          rw [h2]
          rw [show b - (a + 1) = (b - a) - 1 by ring]
          omega
        exact_mod_cast this
      rcases eq_or_lt_of_le (mem_intList_iff.mp hi).1 with hia | hia
      · rw [← hia]
        exact hfa
      · exact ih (a + 1) b hk' (by omega) (by omega) f g
          (fun j hj => hf j (by rw [mem_intList_iff] at hj ⊢; omega))
          (fun j hj => hg j (by rw [mem_intList_iff] at hj ⊢; omega))
          hrf i (by rw [mem_intList_iff] at hi ⊢; omega)
  exact key _ a b rfl hab hbn f g hf hg heq

theorem aptSeg_isGeodesic {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) {a : ℤ} {k : ℕ} (hk : k ≤ n) :
    (aptSeg ht.2 a k hk).IsGeodesic :=
  CFSG.Quasithin.H13.F431.F45.nb_dist
    (isGenPolygon_of_isGeneralizedPolygon (by omega) hP hT) hk (aptSeg ht.2 a k hk)
    (aptSeg_noBack (by omega) ht a hk)

theorem aptSegRev_isGeodesic {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) {a : ℤ} {k : ℕ} (hk : k ≤ n) :
    (aptSegRev ht.2 a k hk).IsGeodesic :=
  CFSG.Quasithin.H13.F431.F45.nb_dist
    (isGenPolygon_of_isGeneralizedPolygon (by omega) hP hT) hk (aptSegRev ht.2 a k hk)
    (aptSegRev_noBack (by omega) ht a hk)

theorem aptRoot_fix_prev {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    {g : D} {k : ℤ} (hg : g ∈ aptRoot D Γ n t (k + (n : ℤ))) :
    g • apt t (k - 1) = apt t (k - 1) := by
  have h := aptRoot_fix ht hg hn (r := (n : ℤ) - 1) (by omega) (by omega)
  rw [show k + (n : ℤ) + ((n : ℤ) - 1) = (k - 1) + 2 * (n : ℤ) * 1 by ring,
    apt_add_two_mul] at h
  exact h

theorem aptRoot_fix_shift {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    {g : D} {k : ℤ} (hg : g ∈ aptRoot D Γ n t (k + (n : ℤ))) : g • apt t k = apt t k := by
  have h := aptRoot_fix ht hg hn (r := (n : ℤ)) (by omega) (by omega)
  rw [show k + (n : ℤ) + (n : ℤ) = k + 2 * (n : ℤ) * 1 by ring, apt_add_two_mul] at h
  exact h

theorem exists_reflection_apt {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) (hM : MoufangCondition D Γ n) {i : ℤ}
    {u : D} (hu : u ∈ aptRoot D Γ n t i) (hu1 : u ≠ 1) :
    ∃ v ∈ aptRoot D Γ n t (i + (n : ℤ)), ∃ w ∈ aptRoot D Γ n t (i + (n : ℤ)),
      (∀ k : ℤ, (v * u * w) • apt t k = apt t (2 * i - k)) ∧
      (∀ j : ℤ, (aptRoot D Γ n t j).map (MulAut.conj (v * u * w)).toMonoidHom =
        aptRoot D Γ n t (2 * i + (n : ℤ) - j)) := by
  classical
  have hgp : IsGenPolygon Γ n := isGenPolygon_of_isGeneralizedPolygon (by omega) hP hT
  have huf : ∀ r : ℤ, i ≤ r → r ≤ i + (n : ℤ) → u • apt t r = apt t r := by
    intro r h1 h2
    have h := aptRoot_fix ht hu hn (r := r - i) (by omega) (by omega)
    rwa [show i + (r - i) = r by ring] at h
  have huif : ∀ r : ℤ, i ≤ r → r ≤ i + (n : ℤ) → u⁻¹ • apt t r = apt t r :=
    fun r h1 h2 => inv_smul_eq_iff.mpr (huf r h1 h2).symm
  have hne1 : u • apt t (i - 1) ≠ apt t (i - 1) := by
    intro h
    refine hu1 (aptRoot_eq_one_of_fix_adj_start ht hu hn hP hT ?_ ?_ h)
    · have h2 := (apt_adj ht (i - 1)).symm
      rwa [show i - 1 + 1 = i by ring] at h2
    · have h2 := apt_ne_two (by omega : 2 ≤ n) ht (i - 1)
      rwa [show i - 1 + 2 = i + 1 by ring] at h2
  have hne2 : u • apt t (i - 1) ≠ apt t (i + 1) := by
    intro h
    have h2 : apt t (i - 1) = u⁻¹ • apt t (i + 1) := by rw [← h]; simp
    rw [show u⁻¹ • apt t (i + 1) = apt t (i + 1) from huif _ (by omega) (by omega)] at h2
    exact apt_ne_two (by omega : 2 ≤ n) ht (i - 1) (by
      rwa [show i - 1 + 2 = i + 1 by ring])
  have hne3 : u⁻¹ • apt t (i - 1) ≠ apt t (i - 1) := by
    intro h
    refine hne1 ?_
    rw [show u • apt t (i - 1) = u • (u⁻¹ • apt t (i - 1)) from by rw [h],
      smul_inv_smul]
  have hne4 : u⁻¹ • apt t (i - 1) ≠ apt t (i + 1) := by
    intro h
    have h2 : apt t (i - 1) = u • apt t (i + 1) := by rw [← h]; simp
    rw [show u • apt t (i + 1) = apt t (i + 1) from huf _ (by omega) (by omega)] at h2
    exact apt_ne_two (by omega : 2 ≤ n) ht (i - 1) (by
      rwa [show i - 1 + 2 = i + 1 by ring])
  have hcent : apt t (i + (n : ℤ) + (n : ℤ)) = apt t i := by
    rw [show i + (n : ℤ) + (n : ℤ) = i + 2 * (n : ℤ) * 1 by ring, apt_add_two_mul]
  have hpen : apt t (i + (n : ℤ) + (n : ℤ) - 1) = apt t (i - 1) := by
    rw [show i + (n : ℤ) + (n : ℤ) - 1 = (i - 1) + 2 * (n : ℤ) * 1 by ring, apt_add_two_mul]
  have hex : ∀ y y' : V, Γ.Adj (apt t i) y → Γ.Adj (apt t i) y' → y ≠ apt t (i - 1) →
      y' ≠ apt t (i - 1) → ∃ g ∈ aptRoot D Γ n t (i + (n : ℤ)), g • y = y' := by
    intro y y' hy hy' h1 h2
    exact aptRoot_exists_smul_of_adj ht hn hM (k := i + (n : ℤ))
      (by rwa [hcent]) (by rwa [hcent]) (by rwa [hpen]) (by rwa [hpen])
  have hti : Γ.Adj (apt t i) (apt t (i + 1)) := apt_adj ht i
  have hpm : apt t (i + 1) ≠ apt t (i - 1) := by
    have h := apt_ne_two (by omega : 2 ≤ n) ht (i - 1)
    rw [show i - 1 + 2 = i + 1 by ring] at h
    exact fun hc => h hc.symm
  have hsrc1 : Γ.Adj (apt t i) (u⁻¹ • apt t (i - 1)) := by
    have h := (GraphAction.adj_smul (Γ := Γ) u⁻¹ (apt t i) (apt t (i - 1))).mpr (by
      have h2 := (apt_adj ht (i - 1)).symm
      rwa [show i - 1 + 1 = i by ring] at h2)
    rwa [show u⁻¹ • apt t i = apt t i from huif i le_rfl (by omega)] at h
  have hsrc2 : Γ.Adj (apt t i) (u • apt t (i - 1)) := by
    have h := (GraphAction.adj_smul (Γ := Γ) u (apt t i) (apt t (i - 1))).mpr (by
      have h2 := (apt_adj ht (i - 1)).symm
      rwa [show i - 1 + 1 = i by ring] at h2)
    rwa [show u • apt t i = apt t i from huf i le_rfl (by omega)] at h
  obtain ⟨w, hw, hw1⟩ := hex (apt t (i + 1)) (u⁻¹ • apt t (i - 1)) hti hsrc1 hpm hne3
  obtain ⟨v, hv, hv1⟩ := hex (u • apt t (i - 1)) (apt t (i + 1)) hsrc2 hti hne1 hpm
  set m : D := v * u * w with hm
  have hw_prev : w • apt t (i - 1) = apt t (i - 1) := aptRoot_fix_prev ht hn hw
  have hv_prev : v • apt t (i - 1) = apt t (i - 1) := aptRoot_fix_prev ht hn hv
  have hw_i : w • apt t i = apt t i := aptRoot_fix_shift ht hn hw
  have hv_i : v • apt t i = apt t i := aptRoot_fix_shift ht hn hv
  have hfix_in : ∀ g : D, g ∈ aptRoot D Γ n t (i + (n : ℤ)) → g • apt t (i + (n : ℤ)) =
      apt t (i + (n : ℤ)) := by
    intro g hg
    simpa using aptRoot_fix ht hg hn (r := 0) (by omega) (by omega)
  have hm_i : m • apt t i = apt t i := by
    rw [hm]
    simp only [mul_smul]
    rw [hw_i, huf i le_rfl (by omega), hv_i]
  have hm_in : m • apt t (i + (n : ℤ)) = apt t (i + (n : ℤ)) := by
    rw [hm]
    simp only [mul_smul]
    rw [hfix_in w hw, huf _ (by omega) le_rfl, hfix_in v hv]
  have hm_p : m • apt t (i + 1) = apt t (i - 1) := by
    rw [hm]
    simp only [mul_smul]
    rw [hw1, show u • (u⁻¹ • apt t (i - 1)) = apt t (i - 1) from smul_inv_smul u _, hv_prev]
  have hm_m : m • apt t (i - 1) = apt t (i + 1) := by
    rw [hm]
    simp only [mul_smul]
    rw [hw_prev, hv1]
  have hfwd : ∀ r : ℤ, i + 1 ≤ r → r ≤ i + (n : ℤ) → m • apt t r = apt t (2 * i - r) := by
    intro r h1 h2
    let p : GPath Γ (n - 1) := aptSeg ht.2 (i + 1) (n - 1) (by omega)
    let q : GPath Γ (n - 1) := aptSegRev ht.2 (i - 1) (n - 1) (by omega)
    have hp : p.IsGeodesic := aptSeg_isGeodesic ht hn hP hT (k := n - 1) (by omega)
    have hq : q.IsGeodesic := aptSegRev_isGeodesic ht hn hP hT (k := n - 1) (by omega)
    have hmp : (m • p).IsGeodesic := GPath.IsGeodesic.smul hP.connected hp m
    have hp0 : p 0 = apt t (i + 1) := by
      show (aptSeg ht.2 (i + 1) (n - 1) (by omega)).toFun 0 = apt t (i + 1)
      rw [aptSeg_apply ht.2 (i + 1) (by omega) (i := 0) (by omega)]
      norm_num
    have hq0 : q 0 = apt t (i - 1) := by
      show (aptSegRev ht.2 (i - 1) (n - 1) (by omega)).toFun 0 = apt t (i - 1)
      rw [aptSegRev_apply ht.2 (i - 1) (by omega) (i := 0) (by omega)]
      norm_num
    have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
    have hpl : p (n - 1) = apt t (i + (n : ℤ)) := by
      show (aptSeg ht.2 (i + 1) (n - 1) (by omega)).toFun (n - 1) = apt t (i + (n : ℤ))
      rw [aptSeg_apply ht.2 (i + 1) (by omega) (i := n - 1) (by omega), hcast]
      congr 1
      ring
    have hql : q (n - 1) = apt t (i + (n : ℤ)) := by
      show (aptSegRev ht.2 (i - 1) (n - 1) (by omega)).toFun (n - 1) = apt t (i + (n : ℤ))
      rw [aptSegRev_apply ht.2 (i - 1) (by omega) (i := n - 1) (by omega), hcast]
      rw [show i - 1 - ((n : ℤ) - 1) = (i + (n : ℤ)) + 2 * (n : ℤ) * (-1) by ring,
        apt_add_two_mul]
    have h0 : (m • p) 0 = q 0 := by
      rw [GPath.smul_apply, hp0, hq0]
      exact hm_p
    have hl : (m • p) (n - 1) = q (n - 1) := by
      rw [GPath.smul_apply, hpl, hql]
      exact hm_in
    have heq : m • p = q := hgp.uniqueGeod (n - 1) (m • p) q hmp hq h0 hl (by omega)
    have hr0 : 0 ≤ r - (i + 1) := by omega
    have hr : (r - (i + 1)).toNat ≤ n - 1 := by
      have h3 : ((r - (i + 1)).toNat : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg hr0]
        rw [show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 by
          rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num]
        omega
      exact_mod_cast h3
    have hval := congrArg (fun (z : GPath Γ (n - 1)) => z ((r - (i + 1)).toNat)) heq
    rw [GPath.smul_apply] at hval
    have hpv : p ((r - (i + 1)).toNat) = apt t (i + 1 + (((r - (i + 1)).toNat) : ℤ)) := by
      show (aptSeg ht.2 (i + 1) (n - 1) (by omega)).toFun ((r - (i + 1)).toNat) = _
      exact aptSeg_apply ht.2 (i + 1) (by omega) hr
    have hqv : q ((r - (i + 1)).toNat) = apt t (i - 1 - (((r - (i + 1)).toNat) : ℤ)) := by
      show (aptSegRev ht.2 (i - 1) (n - 1) (by omega)).toFun ((r - (i + 1)).toNat) = _
      exact aptSegRev_apply ht.2 (i - 1) (by omega) hr
    rw [hpv, hqv] at hval
    rw [show i + 1 + (((r - (i + 1)).toNat) : ℤ) = r by
      rw [Int.toNat_of_nonneg hr0]; ring,
      show i - 1 - (((r - (i + 1)).toNat) : ℤ) = 2 * i - r by
      rw [Int.toNat_of_nonneg hr0]; ring] at hval
    exact hval
  have hbwd : ∀ r : ℤ, i - (n : ℤ) ≤ r → r ≤ i - 1 → m • apt t r = apt t (2 * i - r) := by
    intro r h1 h2
    let p : GPath Γ (n - 1) := aptSegRev ht.2 (i - 1) (n - 1) (by omega)
    let q : GPath Γ (n - 1) := aptSeg ht.2 (i + 1) (n - 1) (by omega)
    have hp : p.IsGeodesic := aptSegRev_isGeodesic ht hn hP hT (k := n - 1) (by omega)
    have hq : q.IsGeodesic := aptSeg_isGeodesic ht hn hP hT (k := n - 1) (by omega)
    have hmp : (m • p).IsGeodesic := GPath.IsGeodesic.smul hP.connected hp m
    have hp0 : p 0 = apt t (i - 1) := by
      show (aptSegRev ht.2 (i - 1) (n - 1) (by omega)).toFun 0 = apt t (i - 1)
      rw [aptSegRev_apply ht.2 (i - 1) (by omega) (i := 0) (by omega)]
      norm_num
    have hq0 : q 0 = apt t (i + 1) := by
      show (aptSeg ht.2 (i + 1) (n - 1) (by omega)).toFun 0 = apt t (i + 1)
      rw [aptSeg_apply ht.2 (i + 1) (by omega) (i := 0) (by omega)]
      norm_num
    have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
    have hpl : p (n - 1) = apt t (i + (n : ℤ)) := by
      show (aptSegRev ht.2 (i - 1) (n - 1) (by omega)).toFun (n - 1) = apt t (i + (n : ℤ))
      rw [aptSegRev_apply ht.2 (i - 1) (by omega) (i := n - 1) (by omega), hcast]
      rw [show i - 1 - ((n : ℤ) - 1) = (i + (n : ℤ)) + 2 * (n : ℤ) * (-1) by ring,
        apt_add_two_mul]
    have hql : q (n - 1) = apt t (i + (n : ℤ)) := by
      show (aptSeg ht.2 (i + 1) (n - 1) (by omega)).toFun (n - 1) = apt t (i + (n : ℤ))
      rw [aptSeg_apply ht.2 (i + 1) (by omega) (i := n - 1) (by omega), hcast]
      congr 1
      ring
    have h0 : (m • p) 0 = q 0 := by
      rw [GPath.smul_apply, hp0, hq0]
      exact hm_m
    have hl : (m • p) (n - 1) = q (n - 1) := by
      rw [GPath.smul_apply, hpl, hql]
      exact hm_in
    have heq : m • p = q := hgp.uniqueGeod (n - 1) (m • p) q hmp hq h0 hl (by omega)
    have hr0 : 0 ≤ i - 1 - r := by omega
    have hr : (i - 1 - r).toNat ≤ n - 1 := by
      have h3 : ((i - 1 - r).toNat : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg hr0]
        rw [show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 by
          rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num]
        omega
      exact_mod_cast h3
    have hval := congrArg (fun (z : GPath Γ (n - 1)) => z ((i - 1 - r).toNat)) heq
    rw [GPath.smul_apply] at hval
    have hpv : p ((i - 1 - r).toNat) = apt t (i - 1 - (((i - 1 - r).toNat) : ℤ)) := by
      show (aptSegRev ht.2 (i - 1) (n - 1) (by omega)).toFun ((i - 1 - r).toNat) = _
      exact aptSegRev_apply ht.2 (i - 1) (by omega) hr
    have hqv : q ((i - 1 - r).toNat) = apt t (i + 1 + (((i - 1 - r).toNat) : ℤ)) := by
      show (aptSeg ht.2 (i + 1) (n - 1) (by omega)).toFun ((i - 1 - r).toNat) = _
      exact aptSeg_apply ht.2 (i + 1) (by omega) hr
    rw [hpv, hqv] at hval
    rw [show i - 1 - (((i - 1 - r).toNat) : ℤ) = r by
      rw [Int.toNat_of_nonneg hr0]; ring,
      show i + 1 + (((i - 1 - r).toNat) : ℤ) = 2 * i - r by
      rw [Int.toNat_of_nonneg hr0]; ring] at hval
    exact hval
  have hrange : ∀ r : ℤ, i - (n : ℤ) ≤ r → r ≤ i + (n : ℤ) → m • apt t r = apt t (2 * i - r) := by
    intro r h1 h2
    by_cases h3 : r ≤ i
    · rcases lt_or_eq_of_le h3 with h4 | h4
      · exact hbwd r (by omega) (by omega)
      · rw [h4, show 2 * i - i = i by ring]
        exact hm_i
    · exact hfwd r (by omega) (by omega)
  have hm_all : ∀ k : ℤ, m • apt t k = apt t (2 * i - k) := by
    intro k
    have hpos : (0 : ℤ) < 2 * (n : ℤ) := by
      have h2 : (0 : ℕ) < 2 * n := by omega
      exact_mod_cast h2
    set s : ℤ := (k - (i - (n : ℤ))) % (2 * (n : ℤ)) with hs
    have hs0 : 0 ≤ s := by
      rw [hs]
      exact Int.emod_nonneg _ hpos.ne'
    have hslt : s < 2 * (n : ℤ) := by
      rw [hs]
      exact Int.emod_lt_of_pos _ hpos
    have hdec : s + 2 * (n : ℤ) * ((k - (i - (n : ℤ))) / (2 * (n : ℤ))) = k - (i - (n : ℤ)) := by
      rw [hs]
      exact Int.emod_add_mul_ediv _ _
    have hk : k = ((i - (n : ℤ)) + s) + 2 * (n : ℤ) * ((k - (i - (n : ℤ))) / (2 * (n : ℤ))) := by
      conv_lhs => rw [show k = (i - (n : ℤ)) + (k - (i - (n : ℤ))) by ring, ← hdec]
      ring
    have h1 : apt t k = apt t ((i - (n : ℤ)) + s) := by
      rw [hk]
      exact apt_add_two_mul (t := t) _ _
    have h2 : apt t (2 * i - k) = apt t (2 * i - ((i - (n : ℤ)) + s)) := by
      have he : 2 * i - k = (2 * i - ((i - (n : ℤ)) + s)) +
          2 * (n : ℤ) * (-((k - (i - (n : ℤ))) / (2 * (n : ℤ)))) := by
        linear_combination hdec
      rw [he]
      exact apt_add_two_mul (t := t) _ _
    rw [h1, h2]
    exact hrange ((i - (n : ℤ)) + s) (by omega) (by omega)
  have hmap : ∀ j : ℤ, (aptRoot D Γ n t j).map (MulAut.conj m).toMonoidHom =
      aptRoot D Γ n t (2 * i + (n : ℤ) - j) := by
    intro j
    rw [aptRoot_map_conj (g := m) (t := t) (k := j)]
    refine Subgroup.ext fun x => ?_
    rw [mem_aptRoot, mem_aptRoot]
    constructor
    · intro h i' hi1 hi2 z hz
      have hi1' : 1 ≤ (n : ℤ) - i' := by omega
      have hi2' : (n : ℤ) - i' ≤ (n : ℤ) - 1 := by omega
      refine h ((n : ℤ) - i') hi1' hi2' z ?_
      show Γ.Adj (m • apt t (j + ((n : ℤ) - i'))) z
      rw [hm_all]
      rw [show 2 * i - (j + ((n : ℤ) - i')) = (2 * i + (n : ℤ) - j + i') +
        2 * (n : ℤ) * (-1) by ring, apt_add_two_mul]
      exact hz
    · intro h i' hi1 hi2 z hz
      have hi1' : 1 ≤ (n : ℤ) - i' := by omega
      have hi2' : (n : ℤ) - i' ≤ (n : ℤ) - 1 := by omega
      have hz' : Γ.Adj (apt t (2 * i - (j + i'))) z := by
        have hh := hz
        change Γ.Adj (m • apt t (j + i')) z at hh
        rwa [hm_all] at hh
      refine h ((n : ℤ) - i') hi1' hi2' z ?_
      rw [show 2 * i + (n : ℤ) - j + ((n : ℤ) - i') = (2 * i - (j + i')) +
        2 * (n : ℤ) * 1 by ring, apt_add_two_mul]
      exact hz'
  exact ⟨v, hv, w, hw, hm_all, hmap⟩

theorem exists_conj_aptRoot {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) (hM : MoufangCondition D Γ n) {i : ℤ}
    {u : D} (hu : u ∈ aptRoot D Γ n t i) (hu1 : u ≠ 1) :
    ∃ v ∈ aptRoot D Γ n t (i + (n : ℤ)), ∃ w ∈ aptRoot D Γ n t (i + (n : ℤ)),
      ∀ j : ℤ, (aptRoot D Γ n t j).map (MulAut.conj (v * u * w)).toMonoidHom =
        aptRoot D Γ n t (2 * i + (n : ℤ) - j) := by
  obtain ⟨v, hv, w, hw, -, hmap⟩ := exists_reflection_apt (t := t) ht hn hP hT hM hu hu1
  exact ⟨v, hv, w, hw, hmap⟩

theorem moufangTitsAxioms (n : ℕ) : MoufangTitsAxioms n := by
  intro V _ Γ _ D _ _ _ _ hn hP hT hM t ht
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    exact aptRoot_ne_bot ht hn hP hT hM k
  · intro i j hij hjn u hu v hv
    exact commutator_mem_iSup ht hn hP hT hM hij hjn hu hv
  · intro i f g hf hg heq
    exact aptRoot_prod_unique ht hn hP hT (a := i + 1) (b := i + (n : ℤ)) (by omega) (by omega)
      hf hg heq
  · intro i u hu hu1
    exact exists_conj_aptRoot ht hn hP hT hM hu hu1

end CFSG.Quasithin.Stroth
