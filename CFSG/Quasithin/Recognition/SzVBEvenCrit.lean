module

public import CFSG.Quasithin.Recognition.SzVBEvenDist

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

section Crit

private theorem eq_of_ne_bot_of_le_of_card_eq_two {C Z : Subgroup G} (hne : C ≠ ⊥) (hle : C ≤ Z)
    (hZ : Nat.card Z = 2) : C = Z := by
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 : Nat.card C ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  have h0 : 0 < Nat.card C := Nat.card_pos
  omega

variable (hC : GeoCtx G₀ G₁ G₂ T V z)

include hC

private theorem commutator_Vv_ne_bot_of_dist (hev : Even (critDist G₀ G₁ G₂ V))
    {x γ : CosetGeom G₀ G₁ G₂} (hx : vtype x = false)
    (hd : CosetGeom.dist x γ = critDist G₀ G₁ G₂ V) (hcrit : ¬ Vv V x ≤ ballStab 1 γ) :
    ⁅Vv V x, Vv V γ⁆ ≠ ⊥ ∧ ⁅Vv V x, Vv V γ⁆ ≤ Vv V x ⊓ Vv V γ := by
  have hyp := hC.hyp
  have hN := hyp.normalizes
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hx
  obtain ⟨γ', rfl⟩ : ∃ γ', γ = g • γ' := ⟨g⁻¹ • γ, by rw [smul_inv_smul]⟩
  have hd' : CosetGeom.dist (γ₀ G₀ G₁ G₂) γ' = critDist G₀ G₁ G₂ V := by
    have h := CosetGeom.dist_smul g (γ₀ G₀ G₁ G₂) γ'
    omega
  have hcrit' : ¬ V ≤ ballStab 1 γ' := fun hle => hcrit (by
    rw [Vv_smul_γ₀ hN, ballStab_smul]
    exact conjSub_mono _ hle)
  obtain ⟨hne0, hle0, -, -⟩ := commutator_V_Vv_of_even hyp (V_ne_bot hC) hev hd' hcrit'
  rw [Vv_smul_γ₀ hN, Vv_smul hN, conjSub_commutator]
  refine ⟨fun h => hne0 ((conjSub_eq_bot_iff _).mp h), ?_⟩
  rw [← conjSub_inf]
  exact conjSub_mono _ hle0

theorem commutator_eq_Zv_of_geo (hev : Even (critDist G₀ G₁ G₂ V))
    (hb : 3 ≤ critDist G₀ G₁ G₂ V) {p : ℕ → CosetGeom G₀ G₁ G₂}
    (hp : IsGeo p (critDist G₀ G₁ G₂ V)) (hp0 : vtype (p 0) = false)
    (hcrit : ¬ Vv V (p 0) ≤ ballStab 1 (p (critDist G₀ G₁ G₂ V))) :
    ⁅Vv V (p 0), Vv V (p (critDist G₀ G₁ G₂ V))⁆ ≠ ⊥ ∧
      ⁅Vv V (p 0), Vv V (p (critDist G₀ G₁ G₂ V))⁆ ≤
        Vv V (p 0) ⊓ Vv V (p (critDist G₀ G₁ G₂ V)) ∧
      ⁅Vv V (p 0), Vv V (p (critDist G₀ G₁ G₂ V))⁆ = Zv z (p 1) ∧
      ⁅Vv V (p 0), Vv V (p (critDist G₀ G₁ G₂ V))⁆ = Zv z (p (critDist G₀ G₁ G₂ V - 1)) := by
  set b := critDist G₀ G₁ G₂ V
  have hadj1 : (graph G₀ G₁ G₂).Adj (p 0) (p 1) := hp.adj (i := 0) (by omega)
  have hadj2 : (graph G₀ G₁ G₂).Adj (p (b - 1)) (p b) := by
    have h := hp.adj (i := b - 1) (by omega)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ b)] at h
  have hpb0 : vtype (p b) = false := (vtype_geo_false_iff hC hp hp0 le_rfl).mpr hev
  have hp1 : vtype (p 1) = true := vtype_eq_true_of_adj hadj1 hp0
  have hpb1 : vtype (p (b - 1)) = true := vtype_eq_true_of_adj hadj2.symm hpb0
  have hd : CosetGeom.dist (p 0) (p b) = b := by
    rw [hp 0 b (Nat.zero_le _) le_rfl]; omega
  have d1 : CosetGeom.dist (p b) (p 1) < b := by
    rw [CosetGeom.dist_comm, hp 1 b (by omega) le_rfl]; omega
  have d2 : CosetGeom.dist (p 0) (p (b - 1)) < b := by
    rw [hp 0 (b - 1) (Nat.zero_le _) (by omega)]; omega
  obtain ⟨hne, hle⟩ := commutator_Vv_ne_bot_of_dist hC hev hp0 hd hcrit
  have hle1 : ⁅Vv V (p 0), Vv V (p b)⁆ ≤ Zv z (p 1) :=
    (Subgroup.commutator_mono (Vv_le_Vv_of_adj hadj1 hp0)
      (Vv_le_pCoreOf_of_dist_lt hC hpb0 d1)).trans (commutator_Vv_pCoreOf_le_Zv hC hp1)
  have hle2 : ⁅Vv V (p 0), Vv V (p b)⁆ ≤ Zv z (p (b - 1)) := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono (Vv_le_Vv_of_adj hadj2.symm hpb0)
      (Vv_le_pCoreOf_of_dist_lt hC hp0 d2)).trans (commutator_Vv_pCoreOf_le_Zv hC hpb1)
  exact ⟨hne, hle, eq_of_ne_bot_of_le_of_card_eq_two hne hle1 (card_Zv hC hp1),
    eq_of_ne_bot_of_le_of_card_eq_two hne hle2 (card_Zv hC hpb1)⟩

theorem exists_crit_geodesic :
    ∃ p : ℕ → CosetGeom G₀ G₁ G₂, IsGeo p (critDist G₀ G₁ G₂ V) ∧ p 0 = γ₀ G₀ G₁ G₂ ∧
      p 1 = γ₁ G₀ G₁ G₂ ∧ ¬ V ≤ ballStab 1 (p (critDist G₀ G₁ G₂ V)) := by
  have hyp := hC.hyp
  have hb0 : 0 < critDist G₀ G₁ G₂ V := (critDist_spec hyp (V_ne_bot hC)).1
  obtain ⟨γ, hγ⟩ := exists_isCriticalVertex hyp (V_ne_bot hC)
  set b := critDist G₀ G₁ G₂ V
  have hdγ : CosetGeom.dist (γ₀ G₀ G₁ G₂) γ = b := hγ.dist_eq
  have hgeo : CosetGeom.dist (γ₁ G₀ G₁ G₂) γ + 1 = b := hγ.geodesic
  obtain ⟨q, hq0, hqn, hq⟩ := exists_geodesic hyp.gen (b - 1) (γ₁ G₀ G₁ G₂) γ (by omega)
  have h01 : CosetGeom.dist (γ₀ G₀ G₁ G₂) (γ₁ G₀ G₁ G₂) = 1 :=
    dist_eq_one_iff_adj.mpr adj_γ₀_γ₁
  let p : ℕ → CosetGeom G₀ G₁ G₂ := fun i => if i = 0 then γ₀ G₀ G₁ G₂ else q (i - 1)
  have hp0 : p 0 = γ₀ G₀ G₁ G₂ := by simp [p]
  have hpq : ∀ i, 1 ≤ i → p i = q (i - 1) := fun i hi => by
    have hi0 : i ≠ 0 := by omega
    simp [p, hi0]
  have hgeoP : IsGeo p b := by
    intro i j hij hjb
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [CosetGeom.dist_self]
      · rw [hp0, hpq j hj]
        have h1 := CosetGeom.dist_triangle hyp.gen (γ₀ G₀ G₁ G₂) (γ₁ G₀ G₁ G₂) (q (j - 1))
        have h2 := hq 0 (j - 1) (Nat.zero_le _) (by omega)
        rw [hq0] at h2
        have h3 := CosetGeom.dist_triangle hyp.gen (γ₀ G₀ G₁ G₂) (q (j - 1)) γ
        have h4 := hq (j - 1) (b - 1) (by omega) le_rfl
        rw [hqn] at h4
        omega
    · rw [hpq i hi, hpq j (by omega), hq (i - 1) (j - 1) (by omega) (by omega)]
      omega
  refine ⟨p, hgeoP, hp0, ?_, ?_⟩
  · rw [hpq 1 le_rfl, Nat.sub_self, hq0]
  · rw [hpq b (by omega), hqn]
    exact hγ.not_le

end Crit

end CFSG.Quasithin.SzVB
