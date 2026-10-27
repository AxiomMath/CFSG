module

public import CFSG.Quasithin.Recognition.SzVBEvenCrit
public import CFSG.Quasithin.Recognition.SzVBEvenLabel

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

section Path

omit [Finite G] in
theorem isGeo_of_walk_dist {q : ℕ → CosetGeom G₀ G₁ G₂} {n : ℕ} (hG : G₀ = G₁ ⊔ G₂)
    (hadj : ∀ i, i < n → (graph G₀ G₁ G₂).Adj (q i) (q (i + 1)))
    (hd : n ≤ CosetGeom.dist (q 0) (q n)) : IsGeo q n := by
  have hle : ∀ i k, i + k ≤ n → CosetGeom.dist (q i) (q (i + k)) ≤ k := by
    intro i k
    induction k with
    | zero => intro _; simp [CosetGeom.dist_self]
    | succ k ih =>
      intro hik
      have h1 := ih (by omega)
      have h2 : CosetGeom.dist (q (i + k)) (q (i + (k + 1))) = 1 :=
        dist_eq_one_iff_adj.mpr (hadj (i + k) (by omega))
      have h3 := CosetGeom.dist_triangle hG (q i) (q (i + k)) (q (i + (k + 1)))
      omega
  intro i j hij hj
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  have h1 := hle i k hj
  have h2 := hle 0 i (by omega)
  have h3 := hle (i + k) (n - (i + k)) (by omega)
  rw [show i + k + (n - (i + k)) = n by omega] at h3
  rw [Nat.zero_add] at h2
  have h4 := CosetGeom.dist_triangle hG (q 0) (q i) (q n)
  have h5 := CosetGeom.dist_triangle hG (q i) (q (i + k)) (q n)
  omega

omit [Finite G] in
theorem exists_isGeo_cons_two (hG : G₀ = G₁ ⊔ G₂) {p : ℕ → CosetGeom G₀ G₁ G₂} {n m : ℕ}
    (hm : m = n + 2) (hp : IsGeo p n) {x β : CosetGeom G₀ G₁ G₂}
    (hxβ : (graph G₀ G₁ G₂).Adj x β) (hβ : (graph G₀ G₁ G₂).Adj β (p 0))
    (hd : CosetGeom.dist x (p n) = m) :
    ∃ q : ℕ → CosetGeom G₀ G₁ G₂, IsGeo q m ∧ q 0 = x ∧ q 1 = β ∧ q m = p n ∧
      ∀ i, q (i + 2) = p i := by
  obtain ⟨q, hq0, hq1, hq2⟩ : ∃ q : ℕ → CosetGeom G₀ G₁ G₂, q 0 = x ∧ q 1 = β ∧
      ∀ i, q (i + 2) = p i :=
    ⟨fun j => if j = 0 then x else if j = 1 then β else p (j - 2), by simp, by simp,
      fun i => by simp only [show i + 2 ≠ 0 by omega, show i + 2 ≠ 1 by omega, ite_false,
        Nat.add_sub_cancel]⟩
  have hqm : q m = p n := by rw [hm]; exact hq2 n
  refine ⟨q, ?_, hq0, hq1, hqm, hq2⟩
  refine isGeo_of_walk_dist hG (fun i hi => ?_) ?_
  · rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      · have e : q (0 + 1) = β := hq1
        rw [e, hq0]
        exact hxβ
      · have e : q (1 + 1) = p 0 := hq2 0
        rw [e, hq1]
        exact hβ
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
      rw [show k + 2 + 1 = (k + 1) + 2 by omega, hq2, hq2]
      exact hp.adj (by omega)
  · rw [hq0, hqm]
    exact hd.ge

end Path

section Geo1

variable (hC : GeoCtx G₀ G₁ G₂ T V z) (hev : Even (critDist G₀ G₁ G₂ V))
  (hb : 3 ≤ critDist G₀ G₁ G₂ V) {p : ℕ → CosetGeom G₀ G₁ G₂}
  (hp : IsGeo p (critDist G₀ G₁ G₂ V)) (hp0 : p 0 = γ₀ G₀ G₁ G₂) (hp1 : p 1 = γ₁ G₀ G₁ G₂)
  (hcrit : ¬ V ≤ ballStab 1 (p (critDist G₀ G₁ G₂ V)))

include hC hev hb hp hp0 hp1 hcrit

private theorem comm_V_Vv_p :
    ⁅V, Vv V (p (critDist G₀ G₁ G₂ V))⁆ ≤ V ⊓ Vv V (p (critDist G₀ G₁ G₂ V)) ∧
      ⁅V, Vv V (p (critDist G₀ G₁ G₂ V))⁆ = Zv z (γ₁ G₀ G₁ G₂) ∧
      ⁅V, Vv V (p (critDist G₀ G₁ G₂ V))⁆ = Zv z (p (critDist G₀ G₁ G₂ V - 1)) := by
  have hV0 : Vv V (p 0) = V := by rw [hp0]; exact Vv_γ₀ hC.hyp.normalizes
  obtain ⟨-, h2, h3, h4⟩ := commutator_eq_Zv_of_geo hC hev hb hp (by rw [hp0]; exact vtype_γ₀)
    (by rw [hV0]; exact hcrit)
  rw [hV0] at h2 h3 h4
  rw [hp1] at h3
  exact ⟨h2, h3, h4⟩

theorem Vv_le_pCoreOf_delta {x : CosetGeom G₀ G₁ G₂} (hx : vtype x = false)
    (hxd : dist x (γ₀ G₀ G₁ G₂) ≤ 2) :
    Vv V x ≤ pCoreOf 2 (stab (p (critDist G₀ G₁ G₂ V - 2))) := by
  have hG := hC.hyp.gen
  have hN := hC.hyp.normalizes
  set b := critDist G₀ G₁ G₂ V with hbdef
  have hb4 : 4 ≤ b := by obtain ⟨k, hk⟩ := id hev; omega
  have hev2 : Even (b - 2) := by obtain ⟨k, hk⟩ := id hev; exact ⟨k - 1, by omega⟩
  have hv : ∀ i, i ≤ b → (vtype (p i) = false ↔ Even i) := fun i hi =>
    vtype_geo_false_iff hC hp (by rw [hp0]; exact vtype_γ₀) hi
  have hvδ : vtype (p (b - 2)) = false := (hv (b - 2) (by omega)).mpr hev2
  by_cases hlt : CosetGeom.dist x (p (b - 2)) < b
  · exact Vv_le_pCoreOf_of_dist_lt hC hx hlt
  by_contra hnot
  have hδ0 : CosetGeom.dist (γ₀ G₀ G₁ G₂) (p (b - 2)) = b - 2 := by
    have := hp 0 (b - 2) (Nat.zero_le _) (by omega)
    rw [hp0] at this
    omega
  have hxδ : CosetGeom.dist x (p (b - 2)) = b := by
    have := dist_triangle hG x (γ₀ G₀ G₁ G₂) (p (b - 2))
    omega
  have hxne : x ≠ γ₀ G₀ G₁ G₂ := by
    intro h
    rw [h] at hxδ
    omega
  have hxγ : CosetGeom.dist x (γ₀ G₀ G₁ G₂) = 2 := by
    have hev' : Even (CosetGeom.dist x (γ₀ G₀ G₁ G₂)) :=
      (vtype_eq_iff_even_dist hG x (γ₀ G₀ G₁ G₂)).mp (by rw [hx, vtype_γ₀])
    have hne0 : CosetGeom.dist x (γ₀ G₀ G₁ G₂) ≠ 0 := fun h =>
      hxne ((dist_eq_zero_iff hG).mp h)
    obtain ⟨k, hk⟩ := hev'
    omega
  obtain ⟨β', hxβ', hγβ'⟩ := exists_adj_dist_eq hG (α := γ₀ G₀ G₁ G₂) (δ := x) (d := 1)
    (by rw [CosetGeom.dist_comm]; omega)
  have hγβ'adj : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β' := dist_eq_one_iff_adj.mp hγβ'
  have hβ'γ₁ : β' ≠ γ₁ G₀ G₁ G₂ := by
    intro h
    rw [h] at hxβ'
    have h1 : CosetGeom.dist x (γ₁ G₀ G₁ G₂) = 1 := dist_eq_one_iff_adj.mpr hxβ'
    have h2 := hp 1 (b - 2) (by omega) (by omega)
    rw [hp1] at h2
    have h3 := dist_triangle hG x (γ₁ G₀ G₁ G₂) (p (b - 2))
    omega
  have hnot' : ¬ Vv V x ≤ ballStab 1 (p (b - 2)) := by
    rw [ballStab_one_eq_pCoreOf hC]
    exact hnot
  obtain ⟨q, hq, hq0, hq1, hqb, hq2⟩ := exists_isGeo_cons_two hG (n := b - 2) (m := b)
    (by omega) (fun i j hij hj => hp i j hij (by omega)) hxβ'
    (by rw [hp0]; exact hγβ'adj.symm) hxδ
  have hq0t : vtype (q 0) = false := by rw [hq0]; exact hx
  have hcq : ¬ Vv V (q 0) ≤ ballStab 1 (q b) := by
    rw [hq0, hqb]
    exact hnot'
  have hcomm : ⁅Vv V (q 0), Vv V (q b)⁆ ≠ ⊥ ∧
      ⁅Vv V (q 0), Vv V (q b)⁆ ≤ Vv V (q 0) ⊓ Vv V (q b) ∧
      ⁅Vv V (q 0), Vv V (q b)⁆ = Zv z (q 1) ∧
      ⁅Vv V (q 0), Vv V (q b)⁆ = Zv z (q (b - 1)) :=
    commutator_eq_Zv_of_geo hC hev hb hq hq0t hcq
  obtain ⟨-, -, hc1, hc2⟩ := hcomm
  have hqb1 : q (b - 1) = p (b - 3) := by
    have := hq2 (b - 3)
    rwa [show b - 3 + 2 = b - 1 by omega] at this
  rw [hq1] at hc1
  rw [hqb1] at hc2
  have hZ1 : Zv z β' = Zv z (p (b - 3)) := hc1.symm.trans hc2
  obtain ⟨-, hcp1, hcp2⟩ := comm_V_Vv_p hC hev hb hp hp0 hp1 hcrit
  have hZ2 : Zv z (γ₁ G₀ G₁ G₂) = Zv z (p (b - 1)) := hcp1.symm.trans hcp2
  have hadj1 : (graph G₀ G₁ G₂).Adj (p (b - 2)) (p (b - 3)) := by
    have h := hp.adj (i := b - 3) (by omega)
    rw [show b - 3 + 1 = b - 2 by omega] at h
    exact h.symm
  have hadj2 : (graph G₀ G₁ G₂).Adj (p (b - 2)) (p (b - 1)) := by
    have h := hp.adj (i := b - 2) (by omega)
    rw [show b - 2 + 1 = b - 1 by omega] at h
    exact h
  have hne1 : p (b - 3) ≠ p (b - 1) := hp.ne (by omega) (by omega)
  have hVδ : Zv z (p (b - 3)) ⊔ Zv z (p (b - 1)) = Vv V (p (b - 2)) :=
    Zv_sup_eq hC hvδ hadj1 hadj2 hne1
  have hVγ : Zv z β' ⊔ Zv z (γ₁ G₀ G₁ G₂) = Vv V (γ₀ G₀ G₁ G₂) :=
    Zv_sup_eq hC vtype_γ₀ hγβ'adj adj_γ₀_γ₁ hβ'γ₁
  have hVV : Vv V (p (b - 2)) = V := by
    rw [← hVδ, ← hZ1, ← hZ2, hVγ, Vv_γ₀ hN]
  have hdδ : CosetGeom.dist (p (b - 2)) (p b) = 2 := by
    have := hp (b - 2) b (by omega) le_rfl
    omega
  have hle : Vv V (p (b - 2)) ≤ pCoreOf 2 (stab (p b)) :=
    Vv_le_pCoreOf_of_dist_lt hC hvδ (by omega)
  rw [hVV] at hle
  apply hcrit
  rw [ballStab_one_eq_pCoreOf hC]
  exact hle

omit hp1 hcrit in
theorem relIndex_Vv_u :
    Vv V (p (critDist G₀ G₁ G₂ V - 1)) ≤ stab (γ₀ G₀ G₁ G₂) ∧
      (pCoreOf 2 (stab (γ₀ G₀ G₁ G₂))).relIndex (Vv V (p (critDist G₀ G₁ G₂ V - 1))) ≤ 2 := by
  set b := critDist G₀ G₁ G₂ V with hbdef
  have hb4 : 4 ≤ b := by obtain ⟨k, hk⟩ := id hev; omega
  have hv : ∀ i, i ≤ b → (vtype (p i) = false ↔ Even i) := fun i hi =>
    vtype_geo_false_iff hC hp (by rw [hp0]; exact vtype_γ₀) hi
  have hvu : vtype (p (b - 1)) = true := by
    have hodd : ¬ Even (b - 1) := by
      obtain ⟨k, hk⟩ := id hev
      rintro ⟨m, hm⟩
      omega
    by_contra hne
    exact hodd ((hv (b - 1) (by omega)).mp (by simpa using hne))
  have hdu : CosetGeom.dist (p (b - 1)) (γ₀ G₀ G₁ G₂) = b - 1 := by
    have := hp 0 (b - 1) (Nat.zero_le _) (by omega)
    rw [hp0] at this
    rw [CosetGeom.dist_comm]
    omega
  have hle : Vv V (p (b - 1)) ≤ stab (γ₀ G₀ G₁ G₂) :=
    Vv_le_stab_of_dist_le_B hC hvu (by omega)
  exact ⟨hle, relIndex_pCoreOf_le_two hC vtype_γ₀ hle
    (F7.isPGroup_of_isElemAbelian (isElemAbelian_Vv_of_vtype hC hvu hb))⟩

theorem inf_Vv_u_eq_Zv :
    V ⊓ Vv V (p (critDist G₀ G₁ G₂ V - 1)) = Zv z (γ₁ G₀ G₁ G₂) := by
  have hN := hC.hyp.normalizes
  set b := critDist G₀ G₁ G₂ V with hbdef
  have hb4 : 4 ≤ b := by obtain ⟨k, hk⟩ := id hev; omega
  have hv : ∀ i, i ≤ b → (vtype (p i) = false ↔ Even i) := fun i hi =>
    vtype_geo_false_iff hC hp (by rw [hp0]; exact vtype_γ₀) hi
  have hvb : vtype (p b) = false := (hv b le_rfl).mpr hev
  have hvu : vtype (p (b - 1)) = true := by
    have hodd : ¬ Even (b - 1) := by
      obtain ⟨k, hk⟩ := id hev
      rintro ⟨m, hm⟩
      omega
    by_contra hne
    exact hodd ((hv (b - 1) (by omega)).mp (by simpa using hne))
  obtain ⟨hcle, hcZ, -⟩ := comm_V_Vv_p hC hev hb hp hp0 hp1 hcrit
  have hZle : Zv z (γ₁ G₀ G₁ G₂) ≤ V ⊓ Vv V (p b) := hcZ.symm.le.trans hcle
  have hadj : (graph G₀ G₁ G₂).Adj (p b) (p (b - 1)) := by
    have h := hp.adj (i := b - 1) (by omega)
    rw [show b - 1 + 1 = b by omega] at h
    exact h.symm
  have hVpb : Vv V (p b) ≤ pCoreOf 2 (stab (p b)) := Vv_le_pCoreOf_stab hC hvb
  have hdu : CosetGeom.dist (p (b - 1)) (p b) = 1 := by
    have := hp (b - 1) b (by omega) le_rfl
    omega
  have hVu : Vv V (p (b - 1)) ≤ pCoreOf 2 (stab (p b)) :=
    Vv_le_pCoreOf_of_dist_lt_B hC hvu (by omega)
  have hVQ : ¬ V ≤ pCoreOf 2 (stab (p b)) := fun h => hcrit (by
    rw [ballStab_one_eq_pCoreOf hC]
    exact h)
  have hd0b : CosetGeom.dist (γ₀ G₀ G₁ G₂) (p b) = b := by
    have := hp 0 b (Nat.zero_le _) le_rfl
    rw [hp0] at this
    omega
  have hVstab : V ≤ stab (p b) := by
    have := Vv_le_stab_of_dist_le hC (x := γ₀ G₀ G₁ G₂) vtype_γ₀ (y := p b) (by omega)
    rwa [Vv_γ₀ hN] at this
  have hrel : (pCoreOf 2 (stab (p b))).relIndex V ≤ 2 :=
    relIndex_pCoreOf_le_two hC hvb hVstab hC.hyp.isPGroup
  have hcard : Nat.card (V ⊓ pCoreOf 2 (stab (p b)) : Subgroup G) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 (stab (p b))) V
    rw [hC.natS3.card_eq, inf_comm] at h1
    have h2 : (pCoreOf 2 (stab (p b))).relIndex V ≠ 1 := fun h =>
      hVQ (Subgroup.relIndex_eq_one.mp h)
    have h3 : (pCoreOf 2 (stab (p b))).relIndex V ≠ 0 := by
      intro h
      rw [h] at h1
      simp at h1
    have h4 : (pCoreOf 2 (stab (p b))).relIndex V = 2 := by omega
    rw [h4] at h1
    omega
  have hZQ : Zv z (γ₁ G₀ G₁ G₂) ≤ V ⊓ pCoreOf 2 (stab (p b)) :=
    le_inf (hZle.trans inf_le_left) (hZle.trans (inf_le_right.trans hVpb))
  have hZeq : Zv z (γ₁ G₀ G₁ G₂) = V ⊓ pCoreOf 2 (stab (p b)) := by
    refine Subgroup.eq_of_le_of_card_ge hZQ ?_
    rw [hcard, card_Zv hC vtype_γ₁]
  apply le_antisymm
  · exact (inf_le_inf le_rfl hVu).trans hZeq.symm.le
  · exact hZle.trans (inf_le_inf le_rfl (Vv_le_Vv_of_adj hadj hvb))

end Geo1

end CFSG.Quasithin.SzVB
