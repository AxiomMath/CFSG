module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3S6Lab
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RCoinc

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

theorem false_of_sixteen_five (h16 : Nat.card (conjClosure V B) = 16)
    (hb : critDist (A ⊔ B) A B V = 5)
    (hF : ∀ s₁ s₂ s₃ : CosetGeom (A ⊔ B) A B, vtype s₂ = true → (graph (A ⊔ B) A B).Adj s₁ s₂ →
      (graph (A ⊔ B) A B).Adj s₂ s₃ → s₁ ≠ s₃ →
        ¬ ballStab 1 s₁ ⊓ ballStab 1 s₂ ≤ ballStab 1 s₃)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false → (graph (A ⊔ B) A B).Adj u β →
      (graph (A ⊔ B) A B).Adj u β' → β ≠ β' → Vv V β ⊓ Vv V β' ≤ Vv V u) : False := by
  have hb' : critDist (A ⊔ B) A B V = 4 + 1 := hb
  obtain ⟨p, hp0, hp, hcrit⟩ := h.exists_crit_geodesic hb'
  have hp5 : IsGeo p 5 := hp
  have ht0 : vtype (p 0) = false := by rw [hp0]; exact vtype_γ₀
  have ht1 : vtype (p 1) = true := hp5.vtype_true_of_odd rfl hp0 (by omega) (by decide)
  have ht2 : vtype (p 2) = false := hp5.vtype_false_of_even rfl hp0 (by omega) (by decide)
  have ht3 : vtype (p 3) = true := hp5.vtype_true_of_odd rfl hp0 (by omega) (by decide)
  have ht4 : vtype (p 4) = false := hp5.vtype_false_of_even rfl hp0 (by omega) (by decide)
  have ht5 : vtype (p 5) = true := hp5.vtype_true_of_odd rfl hp0 le_rfl (by decide)
  have a01 : (graph (A ⊔ B) A B).Adj (p 0) (p 1) := hp5.adj (i := 0) (by omega)
  have a12 : (graph (A ⊔ B) A B).Adj (p 1) (p 2) := hp5.adj (i := 1) (by omega)
  have a23 : (graph (A ⊔ B) A B).Adj (p 2) (p 3) := hp5.adj (i := 2) (by omega)
  have a34 : (graph (A ⊔ B) A B).Adj (p 3) (p 4) := hp5.adj (i := 3) (by omega)
  have a45 : (graph (A ⊔ B) A B).Adj (p 4) (p 5) := hp5.adj (i := 4) (by omega)
  have hd : ∀ i j, i ≤ j → j ≤ 5 → CosetGeom.dist (p i) (p j) = j - i := hp5
  have hdc : ∀ i j, i ≤ j → j ≤ 5 → CosetGeom.dist (p j) (p i) = j - i := fun i j hij hj => by
    rw [CosetGeom.dist_comm]
    exact hd i j hij hj
  have n13 : p 1 ≠ p 3 := hp5.ne (i := 1) (j := 3) (by omega) (by omega)
  have n24 : p 2 ≠ p 4 := hp5.ne (i := 2) (j := 4) (by omega) (by omega)
  have n35 : p 3 ≠ p 5 := hp5.ne (i := 3) (j := 5) (by omega) (by omega)
  have n02 : p 0 ≠ p 2 := hp5.ne (i := 0) (j := 2) (by omega) (by omega)
  have hV0 : Vv V (p 0) = V := by rw [hp0]; exact Vv_γ₀ h.natural.reduced.2.1
  obtain ⟨v, hvV, hvn⟩ := IsConcreteLE.not_le_iff_exists.1 hcrit
  have hv0 : v ∈ Vv V (p 0) := by rw [hV0]; exact hvV
  have hvB : v ∈ ballStab 5 (p 0) := h.Vv_le_ballStab_A hb ht0 hv0
  have hv5 : v ∈ stab (p 5) := ballStab_le_stab_of_dist_le (n := 5)
    (by have := hd 0 5 (by omega) le_rfl; omega) hvB
  have hv4 : v ∈ stab (p 4) := ballStab_le_stab_of_dist_le (n := 5)
    (by have := hd 0 4 (by omega) (by omega); omega) hvB
  let kv : ↥(A ⊔ B) := ⟨v, stab_le (p 5) hv5⟩
  have hkv5 : kv • p 5 = p 5 := smul_eq_of_mem_stab hv5
  have hkv4 : kv • p 4 = p 4 := smul_eq_of_mem_stab hv4
  obtain ⟨μ, μ', hμ, hμ', h4μ, h4μ', hμμ'⟩ := h.exists_two_others a45.symm
  have hμ0 : vtype μ = false := vtype_eq_false_of_adj hμ ht5
  obtain ⟨w, hwV, hw1⟩ := h.exists_Vv_not_mem_Zv hμ0 hμ.symm
  set c : D := v * w * v⁻¹ * w⁻¹ with hc
  have hcP : IsPair z V (p 5) (p 4) c := h.isPair_comm a45.symm hμ h4μ.symm hkv5 hkv4 hvn hwV hw1
  have hc1 : c ≠ 1 := h.isPair_ne_one ht5 hcP
  obtain ⟨g, hg, hg2⟩ := IsConcreteLE.not_le_iff_exists.mp
    (hF (p 4) (p 3) (p 2) ht3 a34.symm a23.symm n24.symm)
  have hg4 : g ∈ stab (p 4) := ballStab_le_stab 1 _ hg.1
  have hg3 : g ∈ stab (p 3) := ballStab_le_stab 1 _ hg.2
  have hg5 : g ∈ stab (p 5) := ballStab_le_stab_of_dist_le (n := 1)
    (dist_eq_one_iff_adj.mpr a45).le hg.1
  have hg2s : g ∈ stab (p 2) := ballStab_le_stab_of_dist_le (n := 1)
    (dist_eq_one_iff_adj.mpr a23.symm).le hg.2
  let kg : ↥(A ⊔ B) := ⟨g, stab_le (p 4) hg4⟩
  have hkg5 : kg • p 5 = p 5 := smul_eq_of_mem_stab hg5
  have hkg4 : kg • p 4 = p 4 := smul_eq_of_mem_stab hg4
  have hkg3 : kg • p 3 = p 3 := smul_eq_of_mem_stab hg3
  have hkg2 : kg • p 2 = p 2 := smul_eq_of_mem_stab hg2s
  obtain ⟨hgne, hgadj, hgn3⟩ := h.smul_nbr_ne (w := p 2) (u := p 3) (μ := p 1) a23 a12.symm
    n13.symm hkg2 hkg3 hg2
  have hcgP : IsPair z V (p 5) (p 4) (g * c * g⁻¹) := h.isPair_conj_fix hkg5 hkg4 hcP
  have hcg1 : g * c * g⁻¹ ≠ 1 := h.isPair_ne_one ht5 hcgP
  have hprod5 : c * (g * c * g⁻¹) ∈ Zv z (p 5) := h.isPair_mul_mem_Zv ht5 a45.symm hcP hcgP
  by_cases hwQ : w ∈ ballStab 1 (p 1)
  ·
    have hwS0 : w ∈ stab (p 0) := ballStab_le_stab_of_dist_le (n := 1)
      (dist_eq_one_iff_adj.mpr a01.symm).le hwQ
    have hwS1 : w ∈ stab (p 1) := ballStab_le_stab 1 _ hwQ
    have hcomm := h.commutator_mem_Zv a01 ht0 ⟨hwS0, hwS1⟩ hv0
    have hcZ : c ∈ Zv z (p 1) := by
      have e : c = (w * v * w⁻¹ * v⁻¹)⁻¹ := by rw [hc]; group
      rw [e]
      exact (Zv z (p 1)).inv_mem hcomm
    have hcgZ : g * c * g⁻¹ ∈ Zv z (kg • p 1) := by
      rw [h.Zv_smul' kg (p 1)]
      exact mul_mem_conjSub hcZ
    exact h.false_of_label_product ht2 ht4 a12.symm a23 hgadj a34.symm a45 hgne.symm n13 hgn3 n35
      hcZ hcgZ hc1 hcg1 hprod5
  ·
    have hwB : w ∈ ballStab 5 μ := h.Vv_le_ballStab_A hb hμ0 hwV
    have hdμ : CosetGeom.dist μ (p 5) = 1 := dist_eq_one_iff_adj.mpr hμ.symm
    have hw1s : w ∈ stab (p 1) := ballStab_le_stab_of_dist_le (n := 5) (by
      have h1 := CosetGeom.dist_triangle (rfl : A ⊔ B = A ⊔ B) μ (p 5) (p 1)
      have h2 := hdc 1 5 (by omega) le_rfl
      omega) hwB
    have hw2s : w ∈ stab (p 2) := ballStab_le_stab_of_dist_le (n := 5) (by
      have h1 := CosetGeom.dist_triangle (rfl : A ⊔ B = A ⊔ B) μ (p 5) (p 2)
      have h2 := hdc 2 5 (by omega) le_rfl
      omega) hwB
    let kw : ↥(A ⊔ B) := ⟨w, stab_le (p 1) hw1s⟩
    have hkw1 : kw • p 1 = p 1 := smul_eq_of_mem_stab hw1s
    have hkw2 : kw • p 2 = p 2 := smul_eq_of_mem_stab hw2s
    have hvZ : v ∉ Zv z (p 1) := by
      intro hvz
      have hv2 : v ∈ Vv V (p 2) := h.Zv_le_Vv a12.symm ht2 hvz
      refine hvn ?_
      refine ballStab_le_ballStab_of_dist rfl (u := p 2) (v := p 5) (n := 5) (m := 1) ?_
        (h.Vv_le_ballStab_A hb ht2 hv2)
      have := hd 2 5 (by omega) le_rfl
      omega
    have hpair : IsPair z V (p 1) (p 2) (w * v * w⁻¹ * v⁻¹) :=
      h.isPair_comm a12 a01.symm n02 hkw1 hkw2 hwQ hv0 hvZ
    have hc12 : IsPair z V (p 1) (p 2) c := by
      have e : c = (w * v * w⁻¹ * v⁻¹)⁻¹ := by rw [hc]; group
      rw [e]
      exact hpair.inv
    have hcg12 : IsPair z V (kg • p 1) (p 2) (g * c * g⁻¹) := by
      have := h.isPair_conj kg hc12
      rwa [hkg2] at this
    by_cases hz1 : c * (g * c * g⁻¹) = 1
    ·
      have hgt : vtype (kg • p 1) = true := vtype_eq_true_of_adj hgadj ht2
      have hcV1 : c ∈ Vv V (p 1) := isPair_mem_Vv ht1 hc12
      have hcgV : g * c * g⁻¹ ∈ Vv V (kg • p 1) := isPair_mem_Vv hgt hcg12
      have hcV2 : c ∈ Vv V (kg • p 1) := by
        have e : c = (g * c * g⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hz1
        rw [e]
        exact (Vv V (kg • p 1)).inv_mem hcgV
      have hc2 : c ∈ Vv V (p 2) :=
        hI1 (p 2) (p 1) (kg • p 1) ht2 a12.symm hgadj hgne.symm (Subgroup.mem_inf.mpr ⟨hcV1, hcV2⟩)
      exact h.isPair_not_mem_Vv h16 ht1 a12 hc12 hc2
    ·
      obtain ⟨q, hq2, hq3⟩ := IsConcreteLE.not_le_iff_exists.mp
        (h.not_ballStab_le_of_left a23 ht2)
      have hq2s : q ∈ stab (p 2) := ballStab_le_stab 1 _ hq2
      have hq3s : q ∈ stab (p 3) := ballStab_le_stab_of_dist_le (n := 1)
        (dist_eq_one_iff_adj.mpr a23).le hq2
      let kq : ↥(A ⊔ B) := ⟨q, stab_le (p 2) hq2s⟩
      have hkq2 : kq • p 2 = p 2 := smul_eq_of_mem_stab hq2s
      have hkq3 : kq • p 3 = p 3 := smul_eq_of_mem_stab hq3s
      obtain ⟨hq4ne, hq4adj, hq4n2⟩ := h.smul_nbr_ne (w := p 3) (u := p 2) (μ := p 4) a23.symm
        a34 n24 hkq3 hkq2 hq3
      obtain ⟨ε, hεV, hε⟩ := h.conj_pair_mul ht2 a12.symm hgadj hc12 hcg12 hq2
      set s : D := c * (g * c * g⁻¹) with hs
      have hsV4 : s ∈ Vv V (p 4) := h.Zv_le_Vv a45 ht4 hprod5
      have hs3 : s ∉ Zv z (p 3) := fun hmem => n35
        (h.eq_of_Zv_eq ht4 a34.symm a45 (h.Zv_eq_of_mem ht3 ht5 hmem hprod5 hz1))
      have hqs : q * s * q⁻¹ ∈ Vv V (kq • p 4) := by
        rw [h.Vv_smul' kq (p 4)]
        exact mul_mem_conjSub hsV4
      have hqs3 : q * s * q⁻¹ ∉ Zv z (p 3) := fun hmem => hs3 ((h.conj_mem_Zv_iff hkq3).mp hmem)
      have hja : q * s * q⁻¹ ∈ Vv V (p 2) ⊔ Subgroup.zpowers s := by
        rw [hε]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hεV)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
      have h8 := h.card_Vv_le_eight ht3 a23.symm a34 hq4adj n24 hq4n2.symm hq4ne.symm hsV4 hs3 hqs
        hqs3 hja
      rw [h.card_Vv_B_of h16 ht3] at h8
      omega

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
