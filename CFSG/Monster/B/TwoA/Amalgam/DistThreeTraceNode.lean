module

public import CFSG.Monster.B.TwoA.Amalgam.DistThreeTrace
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeDefs
public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeTTCore
public import CFSG.Monster.B.TwoA.Amalgam.EightOrbitsPres

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Co2 (v0 wAct_mul wAct_inv_apply)

@[expose] def omegaTwo
    (w v : CVert) : Set CVert :=
  {u | u ∈ cgraph.neighborSet w ∧ {x | ∃ y ∈ vStab w ⊓ vStab v, cvMul u y = x}.ncard = 8064}

@[expose] def DistThreePathFact :
    Prop :=
  (∀ v u : CVert, u ∈ sphereDistThree v → (xSet v u).Nonempty) ∧
    ∀ v w : CVert, w ∈ sphereFour v → cgraph.neighborSet w ∩ sphereDistThree v ⊆ omegaTwo w v

@[expose] def DistThreeBaseTransvFact :
    Prop :=
  ∀ (k : Jhat) (u : CVert), cvOf (jhatS k) ∈ sphereFour cv0 →
    wAct v0 (jhatToKv0 k) Unitary.sigmaW = Unitary.tauW → u ∈ omegaTwo cv0 (cvOf (jhatS k)) →
    ∃ (hu : clabel u ∈ P1) (R : Submodule CFSG.Fischer.F4 Unitary.V6), R ∈ Unitary.ptOrbit 0 ∧
      p1Proj ⟨clabel u, hu⟩ = Unitary.transvU R

theorem clabelS_mul_self'
    (v : CVert) : clabelS v * clabelS v = 1 := by
  obtain ⟨g, rfl⟩ := cvOf_surjective v
  apply Subtype.ext
  change clabel (cvOf g) * clabel (cvOf g) = 1
  rw [clabel_cvOf]
  calc (g : Dfull)⁻¹ * cQ * g * ((g : Dfull)⁻¹ * cQ * g) = (g : Dfull)⁻¹ * (cQ * cQ) * g := by
        group
    _ = 1 := by rw [cQ_mul_self, mul_one, inv_mul_cancel]

theorem clabelS_ne_one
    (v : CVert) : clabelS v ≠ 1 := by
  obtain ⟨g, rfl⟩ := cvOf_surjective v
  intro h
  have h1 : clabel (cvOf g) = 1 := congrArg Subtype.val h
  rw [clabel_cvOf] at h1
  apply cQ_ne_one
  calc cQ = (g : Dfull) * ((g : Dfull)⁻¹ * cQ * g) * (g : Dfull)⁻¹ := by group
    _ = 1 := by rw [h1, mul_one, mul_inv_cancel]

private theorem clabelS_mem_vStab_self
    (v : CVert) : clabelS v ∈ vStab v := by
  obtain ⟨g, rfl⟩ := cvOf_surjective v
  rw [mem_vStab, cvMul_cvOf, cvOf_eq_iff]
  have e : ((g * (g * clabelS (cvOf g))⁻¹ : Shat) : Dfull) = cQ⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_clabelS, clabel_cvOf]
    group
  rw [e]
  exact Eam.inv_mem cQ_mem_Eam

theorem vStab_le_centralizer
    (u : CVert) : vStab u ≤ Subgroup.centralizer {clabelS u} := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := clabelS_cvMul u y
  rw [mem_vStab.1 hy] at h
  calc y * clabelS u = y * (y⁻¹ * clabelS u * y) := by rw [← h]
    _ = clabelS u * y := by group

theorem isKleinFour_closure_pair {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : Commute a b) :
    IsKleinFour (Subgroup.closure {a, b}) := by
  have hba : b * a = a * b := hc.eq.symm
  have e1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have e2 : a * b * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha, one_mul]
  have e3 : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb, mul_one]
  have e4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have e5 : a * b * (a * b) = 1 := by rw [← mul_assoc, e2, hb]
  let P : G → Prop := fun x => x = 1 ∨ x = a ∨ x = b ∨ x = a * b
  have hmul : ∀ x y, P x → P y → P (x * y) := by
    rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp only [P, one_mul, mul_one, ha, hb, hba, e1, e2, e3, e4, e5, true_or, or_true]
  have hinv : ∀ x, P x → P x⁻¹ := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right ha))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hb)))
    · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right e5)))
  let K : Subgroup G :=
    { carrier := {x | P x}
      mul_mem' := fun hx hy => hmul _ _ hx hy
      one_mem' := Or.inl rfl
      inv_mem' := fun hx => hinv _ hx }
  have hK : Subgroup.closure {a, b} = K := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · rintro x (rfl | rfl | rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have hab1 : a * b ≠ 1 := fun h => hab (by
    calc a = a * (b * b) := by rw [hb, mul_one]
      _ = (a * b) * b := by rw [mul_assoc]
      _ = b := by rw [h, one_mul])
  have haab : a ≠ a * b := fun h => hb1 (by rw [← e1, ← h, ha])
  have hbab : b ≠ a * b := fun h => ha1 (by rw [← e4, ← h, hb])
  have hset : (K : Set G) = {1, a, b, a * b} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rfl
  have hcard : Nat.card K = 4 := by
    rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem,
      Set.ncard_insert_of_notMem, Set.ncard_pair hbab]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hab, haab⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha1.symm, hb1.symm, hab1.symm⟩
  have hsq : ∀ x : K, x ^ 2 = 1 := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one, pow_two]
    rcases hx with rfl | rfl | rfl | rfl
    · exact mul_one 1
    · exact ha
    · exact hb
    · exact e5
  rw [hK]
  refine ⟨hcard, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
    h | h
  · have : Subsingleton K := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : K)
    omega
  · exact h

private theorem mem_sphereFour_comm
    {v w : CVert} : w ∈ sphereFour v ↔ v ∈ sphereFour w := by
  have hord : ∀ a b : CVert, LabelFour a b → LabelFour b a := by
    intro a b h
    have e : lblOrd b a = lblOrd a b := by
      rw [lblOrd, lblOrd, ← MulEquiv.orderOf_eq (MulAut.conj (clabel a)) (clabel b * clabel a),
        MulAut.conj_apply]
      congr 1
      group
    rw [LabelFour, e]
    exact h
  exact ⟨fun h => ⟨SimpleGraph.dist_comm.trans h.1, hord v w h.2⟩,
    fun h => ⟨SimpleGraph.dist_comm.trans h.1, hord w v h.2⟩⟩

theorem exists_normalized_base
    {v w : CVert} (hw : w ∈ sphereFour v) :
    ∃ (g : Shat) (k : Jhat), cvMul w g = cv0 ∧ cvMul v g = cvOf (jhatS k) ∧
      wAct v0 (jhatToKv0 k) Unitary.sigmaW = Unitary.tauW := by
  obtain ⟨s, k, hws, hvs, -, -, hτ⟩ := exists_base_presentation (mem_sphereFour_comm.1 hw)
  refine ⟨s⁻¹, k, ?_, ?_, ?_⟩
  · rw [← hws, cvMul_inv_cancel]
  · rw [← hvs, cvMul_inv_cancel]
  · rw [← psiW_labE]
    exact hτ

theorem cvMul_clabelS_eq_of_commute
    {k : Jhat} {u : CVert} (hu : clabel u ∈ P1)
    (hc : clabel u * labE k = labE k * clabel u) :
    cvMul (cvOf (jhatS k)) (clabelS u) = cvOf (jhatS k) := by
  set m : Jhat := ⟨clabel u, P1_le_Jhat hu⟩ with hm
  have hmS : jhatS m = clabelS u := rfl
  have e1 : cvMul (cvOf (jhatS k)) (clabelS u) = cvOf (jhatS (k * m)) := by
    rw [← hmS, cvMul_jhatS]
  rw [e1]
  apply labE_eq_iff.1
  apply Subtype.ext
  change ((k * m : Jhat) : Dfull)⁻¹ * cQ * (k * m : Jhat) = (k : Dfull)⁻¹ * cQ * k
  rw [Subgroup.coe_mul]
  have hc' : (m : Dfull) * ((k : Dfull)⁻¹ * cQ * k) = ((k : Dfull)⁻¹ * cQ * k) * m := hc
  calc ((k : Dfull) * m)⁻¹ * cQ * (k * m) = (m : Dfull)⁻¹ * ((k : Dfull)⁻¹ * cQ * k) * m := by
        group
    _ = (m : Dfull)⁻¹ * (m * ((k : Dfull)⁻¹ * cQ * k)) := by rw [mul_assoc, ← hc']
    _ = (k : Dfull)⁻¹ * cQ * k := by group

theorem clabelS_mem_vStab_of_dist_three
    (hX : DistThreePathFact) (hT : DistThreeBaseTransvFact)
    {v u : CVert} (hvu : u ∈ sphereDistThree v) :
    clabelS u ∈ vStab v ∧ clabelS v * clabelS u = clabelS u * clabelS v ∧
      clabelS v ≠ clabelS u := by
  obtain ⟨w, hwu, hwv⟩ := hX.1 v u hvu
  obtain ⟨g, k, hwg, hvg, hτ⟩ := exists_normalized_base hwv
  set u₁ := cvMul u g with hu₁
  have h4 : cvOf (jhatS k) ∈ sphereFour cv0 := by
    rw [← hwg, ← hvg]
    exact sphereFour_cvMul (mem_sphereFour_comm.1 hwv) g
  have hadj : u₁ ∈ cgraph.neighborSet cv0 := by
    rw [← hwg, hu₁, SimpleGraph.mem_neighborSet, cgraph_adj_cvMul]
    exact hwu.symm
  have hd : u₁ ∈ sphereDistThree (cvOf (jhatS k)) := by
    rw [← hvg, hu₁]
    exact sphereDistThree_cvMul hvu g
  have hΩ : u₁ ∈ omegaTwo cv0 (cvOf (jhatS k)) :=
    hX.2 (cvOf (jhatS k)) cv0 (mem_sphereFour_comm.1 h4) ⟨hadj, hd⟩
  obtain ⟨hP, R, hR, hsR⟩ := hT k u₁ h4 hτ hΩ
  have hr : psiW (labE k) = Unitary.tauW := by rw [psiW_labE, hτ]
  have hcomm := distThree_trace_bridge_base hP rfl hR hsR hr
  have hfix := cvMul_clabelS_eq_of_commute hP hcomm
  have hne₁ : clabelS (cvOf (jhatS k)) ≠ clabelS u₁ := by
    intro h
    have h1 : (labE k : Dfull) = clabel u₁ := congrArg Subtype.val h
    have h2 : jhatToKv0 ⟨clabel u₁, P1_le_Jhat hP⟩ = 1 := by
      have := jhatToKv0_eq_one_of_mem_Ehat (g := (labE k : Dfull))
        (Ehat_le_Jhat (labE k).2) (labE k).2
      convert this using 3
      exact h1.symm
    have h3 : (Unitary.transvU R : Kstab v0) = 1 := by
      rw [← h2, ← coe_p1Proj ⟨clabel u₁, hP⟩, hsR]
    have h6 := Unitary.finrank_range_transvU (Unitary.fixTauPts_eq ▸ hR).1
    rw [h3, Co2.wAct_one, sub_self, LinearMap.range_zero, finrank_bot] at h6
    exact absurd h6 (by norm_num)
  have hv : v = cvMul (cvOf (jhatS k)) g⁻¹ := by rw [← hvg, cvMul_inv_cancel]
  have hu : u = cvMul u₁ g⁻¹ := by rw [hu₁, cvMul_inv_cancel]
  have hlu : clabelS u = g * clabelS u₁ * g⁻¹ := by
    rw [hu, clabelS_cvMul, inv_inv]
  have hlv : clabelS v = g * clabelS (cvOf (jhatS k)) * g⁻¹ := by
    rw [hv, clabelS_cvMul, inv_inv]
  have hcomm' : clabelS (cvOf (jhatS k)) * clabelS u₁ = clabelS u₁ * clabelS (cvOf (jhatS k)) :=
    Subtype.ext hcomm.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_vStab, hv, hlu, ← cvMul_mul]
    have e : g⁻¹ * (g * clabelS u₁ * g⁻¹) = clabelS u₁ * g⁻¹ := by group
    rw [e, cvMul_mul, hfix]
  · rw [hlu, hlv]
    calc g * clabelS (cvOf (jhatS k)) * g⁻¹ * (g * clabelS u₁ * g⁻¹)
        = g * (clabelS (cvOf (jhatS k)) * clabelS u₁) * g⁻¹ := by group
      _ = g * (clabelS u₁ * clabelS (cvOf (jhatS k))) * g⁻¹ := by rw [hcomm']
      _ = g * clabelS u₁ * g⁻¹ * (g * clabelS (cvOf (jhatS k)) * g⁻¹) := by group
  · rw [hlu, hlv]
    intro h
    apply hne₁
    calc clabelS (cvOf (jhatS k)) = g⁻¹ * (g * clabelS (cvOf (jhatS k)) * g⁻¹) * g := by group
      _ = g⁻¹ * (g * clabelS u₁ * g⁻¹) * g := by rw [h]
      _ = clabelS u₁ := by group

theorem native_distance_three_labels_commute_and_fix_endpoints_of
    (hX : DistThreePathFact)
    (hT : DistThreeBaseTransvFact) {v u : CVert} (hvu : u ∈ sphereDistThree v) :
    clabelS u ∈ vStab v ∧ clabelS v ∈ vStab u ∧ clabelS v ≠ clabelS u ∧
      clabelS v * clabelS v = 1 ∧ clabelS u * clabelS u = 1 ∧ clabelS v ≠ 1 ∧
      clabelS u ≠ 1 ∧ Commute (clabelS v) (clabelS u) ∧
      IsKleinFour (Subgroup.closure {clabelS v, clabelS u}) ∧
      Subgroup.closure {clabelS v, clabelS u} ≤ vStab v ⊓ vStab u ∧
      vStab v ⊓ vStab u ≤ vStab v ⊓ Subgroup.centralizer {clabelS u} := by
  have huv : v ∈ sphereDistThree u := by
    rw [mem_sphereDistThree, SimpleGraph.dist_comm]
    exact hvu
  obtain ⟨h1, hc, hne⟩ := clabelS_mem_vStab_of_dist_three hX hT hvu
  obtain ⟨h2, -, -⟩ := clabelS_mem_vStab_of_dist_three hX hT huv
  refine ⟨h1, h2, hne, clabelS_mul_self' v, clabelS_mul_self' u, clabelS_ne_one v,
    clabelS_ne_one u, hc, isKleinFour_closure_pair (clabelS_mul_self' v) (clabelS_mul_self' u)
      (clabelS_ne_one v) (clabelS_ne_one u) hne hc, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨clabelS_mem_vStab_self _, h2⟩
    · exact ⟨h1, clabelS_mem_vStab_self _⟩
  · exact fun y hy => ⟨hy.1, vStab_le_centralizer u hy.2⟩

end CFSG.Monster.B.TwoA.Amalgam
