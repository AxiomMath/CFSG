module

public import CFSG.Sporadic.Co2Smith.GlWChart

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem glWRelsD_cases : ∀ w ∈ Native.glWRelsD, w = [6, 6] ∨ ∀ k ∈ w, k < 6 := by decide

theorem glWD0_lt : ∀ k ∈ Native.glWD0, k < 6 := by decide

theorem glWRelTri_eq : Native.glWRelTri =
    (Native.glWD0 ++ [6]) ++ ((Native.glWD0 ++ [6]) ++ (Native.glWD0 ++ [6])) := rfl

theorem lt_six_conj {u : List ℕ} (hu : ∀ k ∈ u, k < 6) :
    ∀ k ∈ Native.glWh ++ u ++ Native.glWh.reverse, k < 6 := by
  intro k hk
  rcases List.mem_append.1 hk with hk | hk
  · rcases List.mem_append.1 hk with hk | hk
    · exact glWh_lt k hk
    · exact hu k hk
  · exact glWh_lt k (List.mem_reverse.1 hk)

theorem δ0δ1_cube :
    δ0hK * δ1hK * (δ0hK * δ1hK * (δ0hK * δ1hK)) = 1 := by
  have h := lWord_w7_rel (w := Native.glWRelTri)
    (List.mem_append_right _ (List.mem_singleton_self _))
  have e : lWord w7Letters (Native.glWD0 ++ [6]) = δ0hK * δ1hK := by
    rw [lWord_append, lWord_w7_eq_gen glWD0_lt, ← δ0hK_eq, lWord, lWord, w7Letters_elt_six,
      mul_one]
  rw [glWRelTri_eq, lWord_append w7Letters (Native.glWD0 ++ [6]),
    lWord_append w7Letters (Native.glWD0 ++ [6]) (Native.glWD0 ++ [6]), e] at h
  exact h

theorem transp_of_comm {y : K}
    (hN : y ∈ normalizer (Jc : Set K)) (hC : y ∈ Cz) (hh : hwK * y = y * hwK)
    (hd : δ1hK * y = y * δ1hK) :
    hwKi * y * hwK ∈ normalizer (Jc : Set K) ∧ δ1hK * y * δ1hK⁻¹ ∈ Cz :=
  ⟨by rw [hwKi_conj_of_comm hh]; exact hN, by rw [δ1hK_conj_of_comm hd]; exact hC⟩

section Filter

variable
  {G : Type} [Group G] {z : G} {φ : centralizer ({z} : Set G) ≃* Cz}
  {ψ : normalizer (Jc : Set K) →* G}

theorem cG_mem (hψ : IsNJChart φ ψ) (hz : phiH φ z0C = z) :
    (dG ψ)⁻¹ * d2G φ ψ ∈ centralizer ({z} : Set G) := by
  have hz0' : hwKi * (z0C : K) * hwK ∈ normalizer (Jc : Set K) := by
    show hwKi * z0 * hwK ∈ normalizer (Jc : Set K)
    rw [hwKi_conj_of_comm (comm_of_mem_Cz hwK_mem_Cz)]
    exact Jc_le_N z0_mem_Jc
  have hz0d : δ1hK * (z0C : K) * δ1hK⁻¹ ∈ Cz := by
    show δ1hK * z0 * δ1hK⁻¹ ∈ Cz
    rw [← x25K_eq_conj]
    exact x25K_mem_CzJ
  have h := cG_comm hψ z0C (Jc_le_N z0_mem_Jc) hz0' hz0d
  rw [hz] at h
  exact mem_centralizer_singleton_iff.2 h

theorem cG_comm_E2 (hψ : IsNJChart φ ψ) (hz : phiH φ z0C = z) {j : ℕ} (hj : j < 4) :
    (dG ψ)⁻¹ * d2G φ ψ *
        phiH φ (gwWord (Native.glWh ++ Native.glWE1w[j]! ++ Native.glWh.reverse)) =
      phiH φ (gwWord (Native.glWh ++ Native.glWE1w[j]! ++ Native.glWh.reverse)) *
        ((dG ψ)⁻¹ * d2G φ ψ) := by
  obtain ⟨c', hcc⟩ : ∃ c' : Cz, phiH φ c' = (dG ψ)⁻¹ * d2G φ ψ :=
    ⟨φ ⟨_, cG_mem hψ hz⟩, phiH_apply_symm φ _ _⟩
  have key : ∀ b : Cz, (b : K) ∈ normalizer (Jc : Set K) →
      hwKi * b * hwK ∈ normalizer (Jc : Set K) → δ1hK * b * δ1hK⁻¹ ∈ Cz →
        (c' : K) * b = b * c' := by
    intro b hb hb' hbd
    have h := cG_comm hψ b hb hb' hbd
    rw [← hcc, phiH_comm_iff] at h
    exact congrArg Subtype.val h
  have hKC := mem_C0c.1 (mem_inf.1 hwK_mem_D).1
  have hδC := mem_C0c.1 δ1hK_mem_C0c
  have tα := transp_of_comm α3K_mem_N α3K_mem_Cz hKC.1.symm hδC.1.symm
  have tγ := transp_of_comm γ3K_mem_N γ3K_mem_Cz hKC.2.symm hδC.2.symm
  have hα := key α3c α3K_mem_N tα.1 tα.2
  have hγ := key γ3c γ3K_mem_N tγ.1 tγ.2
  have hD : (c' : K) ∈ C0c ⊓ Cz := mem_inf.2 ⟨mem_C0c.2 ⟨hα.symm, hγ.symm⟩, c'.2⟩
  have hx : (c' : K) * x25K = x25K * c' := by
    refine key ⟨x25K, x25K_mem_CzJ⟩ (Jc_le_N x25K_mem_Jc) ?_ ?_
    · show hwKi * x25K * hwK ∈ normalizer (Jc : Set K)
      rw [hwKi_conj_of_comm hwK_comm_x25K]
      exact Jc_le_N x25K_mem_Jc
    · show δ1hK * x25K * δ1hK⁻¹ ∈ Cz
      rw [δ1hK_conj_x25K]
      exact z0_mem_Cz
  have hJ : ∀ k < Native.glWbJ.length, (c' : K) * bJK k = bJK k * c' := fun k hk =>
    key ⟨bJK k, Jc_le_Cz (jcElt_mem _)⟩ (Jc_le_N (jcElt_mem _)) (bJK_conj_mem_N hk)
      (Jc_le_Cz (conj_δ1hK_mem_Jc (jcElt_mem _)))
  have hQ : ∀ k < Native.glWbQ.size, (c' : K) * bQK k = bQK k * c' := fun k hk =>
    key ⟨bQK k, bQK_mem_Cz hk⟩ (bQK_mem_N hk) (bQK_conj_mem_N hk)
      (conj_δ1hK_mem_Cz (bQK_comm_x25K hk))
  have hE := filter_spec hD hx hJ hQ hj
  have hEv : (gwWord (Native.glWh ++ Native.glWE1w[j]! ++ Native.glWh.reverse) : K) =
      hwK * e1K j * hwKi := by
    rw [gwWord_append, gwWord_append, Subgroup.coe_mul, Subgroup.coe_mul, gwWord_glWh,
      gwWord_E1 hj, gwWord_glWh_rev]
  have hc : c' * gwWord (Native.glWh ++ Native.glWE1w[j]! ++ Native.glWh.reverse) =
      gwWord (Native.glWh ++ Native.glWE1w[j]! ++ Native.glWh.reverse) * c' := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hEv]
    exact hE
  have h := (phiH_comm_iff φ).2 hc
  rwa [hcc] at h

theorem dG_conj_E2 (hψ : IsNJChart φ ψ) (hz : phiH φ z0C = z) {j : ℕ} (hj : j < 4) :
    dG ψ * phiH φ (gwWord (Native.glWh ++ Native.glWE1w[j]! ++ Native.glWh.reverse)) *
        (dG ψ)⁻¹ =
      phiH φ (gwWord (Native.glWh ++ Native.glWE1iw[j]! ++ Native.glWh.reverse)) := by
  have hc := cG_comm_E2 hψ hz hj
  have h2 : d2G φ ψ * phiH φ (gwWord (Native.glWh ++ Native.glWE1w[j]! ++ Native.glWh.reverse)) *
      (d2G φ ψ)⁻¹ =
        phiH φ (gwWord (Native.glWh ++ Native.glWE1iw[j]! ++ Native.glWh.reverse)) := by
    simp only [gwWord_append, gwWord_reverse, map_mul, map_inv, d2G]
    rw [← dG_conj_E1 hψ hj]
    group
  rw [← h2]
  calc dG ψ * phiH φ (gwWord (Native.glWh ++ Native.glWE1w[j]! ++ Native.glWh.reverse)) *
        (dG ψ)⁻¹ =
      dG ψ * (phiH φ (gwWord (Native.glWh ++ Native.glWE1w[j]! ++ Native.glWh.reverse)) *
        ((dG ψ)⁻¹ * d2G φ ψ)) * (d2G φ ψ)⁻¹ := by group
    _ = dG ψ * ((dG ψ)⁻¹ * d2G φ ψ *
        phiH φ (gwWord (Native.glWh ++ Native.glWE1w[j]! ++ Native.glWh.reverse))) *
          (d2G φ ψ)⁻¹ := by rw [hc]
    _ = d2G φ ψ * phiH φ (gwWord (Native.glWh ++ Native.glWE1w[j]! ++ Native.glWh.reverse)) *
        (d2G φ ψ)⁻¹ := by group

end Filter

@[expose] noncomputable def δ0N :
    normalizer (Jc : Set K) :=
  ⟨δ0hK, δ0hK_mem_N⟩

section GLetters

variable
  {G : Type} [Group G] {z : G} (φ : centralizer ({z} : Set G) ≃* Cz)
  (ψ : normalizer (Jc : Set K) →* G)

@[expose] noncomputable def gLet (k : ℕ) : G := if k = 6 then dG ψ else phiH φ (gwLet k)

theorem gLet_six : gLet φ ψ 6 = dG ψ := ite_eq_left rfl

theorem gLet_of_ne {k : ℕ} (hk : k ≠ 6) : gLet φ ψ k = phiH φ (gwLet k) := ite_eq_right hk

theorem gLet_mul_self (k : ℕ) : gLet φ ψ k * gLet φ ψ k = 1 := by
  by_cases hk : k = 6
  · rw [hk, gLet_six, dG_mul_self]
  · rw [gLet_of_ne φ ψ hk, ← map_mul, gwLet_mul_self, map_one]

theorem gLet_inv (k : ℕ) : (gLet φ ψ k)⁻¹ = gLet φ ψ k :=
  inv_eq_of_mul_eq_one_right (gLet_mul_self φ ψ k)

theorem gWord_of_lt {w : List ℕ} (hw : ∀ k ∈ w, k < 6) :
    (w.map (gLet φ ψ)).prod = phiH φ (gwWord w) := by
  rw [gwWord, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [Function.comp_apply, gLet_of_ne φ ψ (by have := hw k hk; omega)]

theorem gWord_reverse : ∀ w : List ℕ,
    (w.reverse.map (gLet φ ψ)).prod = ((w.map (gLet φ ψ)).prod)⁻¹
  | [] => by rw [List.reverse_nil, List.map_nil, List.prod_nil, inv_one]
  | k :: w => by
    simp only [List.reverse_cons, List.map_append, List.prod_append, gWord_reverse w,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_inv_rev, gLet_inv]

theorem gWord_conjRel {u v : List ℕ} (hu : ∀ k ∈ u, k < 6) (hv : ∀ k ∈ v, k < 6)
    (h : dG ψ * phiH φ (gwWord u) * (dG ψ)⁻¹ = phiH φ (gwWord v)) :
    ((Native.glWConjRel u v).map (gLet φ ψ)).prod = 1 := by
  have h' : dG ψ * phiH φ (gwWord u) * dG ψ = phiH φ (gwWord v) := by rw [← h, dG_inv]
  rw [Native.glWConjRel, List.map_append, List.map_append, List.map_append, List.prod_append,
    List.prod_append, List.prod_append, gWord_reverse, gWord_of_lt φ ψ hu, gWord_of_lt φ ψ hv]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, gLet_six]
  rw [h', mul_inv_cancel]

variable {φ ψ}

theorem phiH_δ0 (hψ : IsNJChart φ ψ) (hD0 : δ0hK ∈ Cz) :
    phiH φ ⟨δ0hK, hD0⟩ = ψ δ0N :=
  (hψ δ0N hD0).symm

theorem gWord_D0 (hψ : IsNJChart φ ψ) :
    ((Native.glWD0 ++ [6]).map (gLet φ ψ)).prod = ψ (δ0N * δN) := by
  have hD0 : δ0hK ∈ Cz := gwWord_D0 ▸ (gwWord Native.glWD0).2
  have e1 : phiH φ (gwWord Native.glWD0) = ψ δ0N := by
    rw [← phiH_δ0 hψ hD0]
    exact congrArg (phiH φ) (Subtype.ext gwWord_D0)
  rw [List.map_append, List.prod_append, gWord_of_lt φ ψ glWD0_lt, map_mul, e1]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, gLet_six]
  rfl

end GLetters

section Rel

variable
  {G : Type} [Group G] {z : G} {φ : centralizer ({z} : Set G) ≃* Cz}
  {ψ : normalizer (Jc : Set K) →* G}

theorem gLet_rel (hψ : IsNJChart φ ψ) (hz : phiH φ z0C = z) {w : List ℕ}
    (hw : w ∈ Native.glWRelsN) : (w.map (gLet φ ψ)).prod = 1 := by
  rcases List.mem_append.1 hw with hw1 | hT
  · rcases List.mem_append.1 hw1 with hw2 | hE2
    · rcases List.mem_append.1 hw2 with hD | hE1
      · rcases glWRelsD_cases w hD with rfl | hlt
        · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            gLet_six, dG_mul_self]
        · rw [gWord_of_lt φ ψ hlt, gwWord_eq_one hw hlt, map_one]
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hE1
        have hj' := List.mem_range.1 hj
        exact gWord_conjRel φ ψ (glWE1_spec j hj').1 (glWE1_spec j hj').2.1 (dG_conj_E1 hψ hj')
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hE2
      have hj' := List.mem_range.1 hj
      exact gWord_conjRel φ ψ (lt_six_conj (glWE1_spec j hj').1)
        (lt_six_conj (glWE1_spec j hj').2.1) (dG_conj_E2 hψ hz hj')
  · have e : ∀ l₁ l₂ : List ℕ, ((l₁ ++ l₂).map (gLet φ ψ)).prod =
        (l₁.map (gLet φ ψ)).prod * (l₂.map (gLet φ ψ)).prod := fun l₁ l₂ => by
      rw [List.map_append, List.prod_append]
    rw [List.mem_singleton.1 hT, glWRelTri_eq, e (Native.glWD0 ++ [6]),
      e (Native.glWD0 ++ [6]) (Native.glWD0 ++ [6]), gWord_D0 hψ, ← map_mul, ← map_mul,
      show δ0N * δN * (δ0N * δN * (δ0N * δN)) = 1 from Subtype.ext δ0δ1_cube, map_one]

end Rel

end CFSG.Sporadic.Co2Smith
