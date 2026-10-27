module

public import CFSG.Quasithin.EmptyFaithful.S143EA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

section VStruct

variable (h : Hyp1281Two G T M (yOfL22 T M))

include h

theorem exists_three_cycle {g : G} (hg : GoodElt128 T (yOfL22 T M) g) :
    ∃ z a : G, z ∈ quasithinOmegaOneCenter T ∧ z ≠ 1 ∧ a = g * z * g⁻¹ ∧ a ∈ VZ T M ∧
      a ∉ quasithinOmegaOneCenter T ∧ z * z = 1 ∧ a * a = 1 ∧ z * a = a * z ∧
      g * a * g⁻¹ = z * a ∧ g * (z * a) * g⁻¹ = z ∧
      (∀ w ∈ VZ T M, w = 1 ∨ w = z ∨ w = a ∨ w = z * a) := by
  obtain ⟨z, hzZ, hz1, hzall⟩ := h.exists_zgen
  have hzV : z ∈ VZ T M := Hyp1281Two.omegaOneCenter_le_VZ T M hzZ
  have hA := h.almostSpecialHyp_g1
  have hzz : z * z = 1 := by simpa [sq] using hA.sq_eq_one_of_mem_V hzV
  have hgLT : g ∈ yOfL22 T M ⊔ T := Subgroup.mem_sup_left hg.mem
  have hgV : g ∈ Subgroup.normalizer (VZ T M : Set G) := h.LT_le_normalizer_VZ hgLT
  have haV : g * z * g⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp hgV z).mp hzV
  have haZ : g * z * g⁻¹ ∉ quasithinOmegaOneCenter T := by
    intro haZ
    rcases hzall _ haZ with h1 | h1
    · apply hz1
      have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
      rw [this, h1]; group
    · apply hg.not_mem
      have hgc : g ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rcases hzall y hy with rfl | rfl
        · simp
        · calc y * g = (g * y * g⁻¹) * g := by rw [h1]
            _ = g * y := by group
      exact Subgroup.centralizer_le_normalizer _ hgc
  have hcases := h.VZ_cases hzZ hz1 haV haZ
  have haa : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by simpa [sq] using hA.sq_eq_one_of_mem_V haV
  have hza : z * (g * z * g⁻¹) = (g * z * g⁻¹) * z := (hA.commV haV hzV).symm
  have ha1 : g * z * g⁻¹ ≠ 1 := fun he => haZ (he ▸ Subgroup.one_mem _)
  have hg3 : g * g * g ∈ Subgroup.centralizer (VZ T M : Set G) := by
    have := h.pCoreOf_LT_le_centralizer (h.pow_three_mem_pCoreOf_LT hg.mem)
    have e : g ^ 3 = g * g * g := by rw [pow_succ, pow_two]
    rwa [e] at this
  have hg3z : g * g * g * z * (g * g * g)⁻¹ = z := by
    have := Subgroup.mem_centralizer_iff.mp hg3 z hzV
    calc g * g * g * z * (g * g * g)⁻¹ = (z * (g * g * g)) * (g * g * g)⁻¹ := by rw [← this]
      _ = z := by group
  have hga : g * (g * z * g⁻¹) * g⁻¹ = z * (g * z * g⁻¹) := by
    have hmem : g * (g * z * g⁻¹) * g⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp hgV _).mp haV
    rcases hcases _ hmem with h1 | h1 | h1 | h1
    · exfalso
      apply ha1
      have : g * z * g⁻¹ = g⁻¹ * (g * (g * z * g⁻¹) * g⁻¹) * g := by group
      rw [this, h1]; group
    · exfalso
      apply haZ
      have e : g * z * g⁻¹ = g * g * g * z * (g * g * g)⁻¹ := by
        have : g * g * g * z * (g * g * g)⁻¹ = g * (g * (g * z * g⁻¹) * g⁻¹) * g⁻¹ := by group
        rw [this, h1]
      rw [e, hg3z]; exact hzZ
    · exfalso
      apply haZ
      have h2 : g * z * g⁻¹ = z := by
        calc g * z * g⁻¹ = g⁻¹ * (g * (g * z * g⁻¹) * g⁻¹) * g := by group
          _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [h1]
          _ = z := by group
      rw [h2]; exact hzZ
    · exact h1
  have hlast : (g * z * g⁻¹) * (z * (g * z * g⁻¹)) = z := by
    generalize g * z * g⁻¹ = a at haa hza ⊢
    calc a * (z * a) = (a * z) * a := (mul_assoc _ _ _).symm
      _ = (z * a) * a := by rw [← hza]
      _ = z * (a * a) := mul_assoc _ _ _
      _ = z := by rw [haa, mul_one]
  refine ⟨z, g * z * g⁻¹, hzZ, hz1, rfl, haV, haZ, hzz, haa, hza, hga, ?_, hcases⟩
  calc g * (z * (g * z * g⁻¹)) * g⁻¹ = (g * z * g⁻¹) * (g * (g * z * g⁻¹) * g⁻¹) := by group
    _ = (g * z * g⁻¹) * (z * (g * z * g⁻¹)) := by rw [hga]
    _ = z := hlast

theorem VZ_le_yOfL22 {g : G} (hg : GoodElt128 T (yOfL22 T M) g) : VZ T M ≤ yOfL22 T M := by
  obtain ⟨z, a, hzZ, hz1, rfl, haV, haZ, hzz, haa, hza, hga, hgza, hcases⟩ :=
    exists_three_cycle h hg
  have hzT : z ∈ T := h.isTwoReducedIn.2 (Hyp1281Two.omegaOneCenter_le_VZ T M hzZ)
  have hzM : z ∈ M := h.inM.2 hzT
  have hzL : z * g * z⁻¹ ∈ yOfL22 T M :=
    (Subgroup.mem_normalizer_iff.mp (h.normal hzM) g).mp hg.mem
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hb : z * (g * z * g⁻¹) ∈ yOfL22 T M := by
    have e : z * (g * z * g⁻¹) = (z * g * z⁻¹) * g⁻¹ := by rw [hzi]; group
    rw [e]
    exact Subgroup.mul_mem _ hzL (Subgroup.inv_mem _ hg.mem)
  have hzL' : z ∈ yOfL22 T M := by
    rw [← hgza]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg.mem hb) (Subgroup.inv_mem _ hg.mem)
  have haL : g * z * g⁻¹ ∈ yOfL22 T M :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg.mem hzL') (Subgroup.inv_mem _ hg.mem)
  intro w hw
  rcases hcases w hw with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact hzL'
  · exact haL
  · exact hb

theorem eq_one_of_conj_eq_of_mem_VZ {g : G} (hg : GoodElt128 T (yOfL22 T M) g) {r : G}
    (hr : r ∈ VZ T M) (hfix : g * r * g⁻¹ = r) : r = 1 := by
  obtain ⟨z, a, hzZ, hz1, rfl, haV, haZ, hzz, haa, hza, hga, hgza, hcases⟩ :=
    exists_three_cycle h hg
  rcases hcases r hr with rfl | rfl | rfl | rfl
  · rfl
  · exfalso
    apply haZ
    rw [hfix]; exact hzZ
  · exfalso
    apply hz1
    have h1 := hga
    rw [hfix] at h1
    generalize g * z * g⁻¹ = a at h1
    have := congrArg (· * a⁻¹) h1
    simpa using this.symm
  · exfalso
    apply haZ
    have h1 := hgza
    rw [hfix] at h1
    generalize g * z * g⁻¹ = a at h1 ⊢
    have h2 : a = 1 := by
      have := congrArg (z⁻¹ * ·) h1
      simpa using this
    rw [h2]; exact Subgroup.one_mem _

end VStruct


section WInL

variable (h : Hyp1281Two G T M (yOfL22 T M)) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))

include h hU

theorem exists_mem_U_not_mem_W :
    ∃ u ∈ uOfL22 T M, u ∉ Hyp1281Two.wOfU T M := by
  obtain ⟨u, huU, huC⟩ : ∃ u ∈ uOfL22 T M, u ∉ Subgroup.centralizer (VZ T M : Set G) := by
    by_contra hall
    push Not at hall
    exact h.not_le_centralizer_VZ_of_nonabelian hU fun u hu => hall u hu
  exact ⟨u, huU, fun hw => huC hw.2⟩

variable {g : G} (hg : GoodElt128 T (yOfL22 T M) g)
  (hEV : Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) g = VZ T M)

include hg hEV

theorem wOfU_le_yOfL22 : Hyp1281Two.wOfU T M ≤ yOfL22 T M := by
  obtain ⟨u, huU, huW⟩ := exists_mem_U_not_mem_W h hU
  have hVL := VZ_le_yOfL22 h hg
  have : ((yOfL22 T M).subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer h.normal
  let π : ↥M →* ↥M ⧸ (yOfL22 T M).subgroupOf M := QuotientGroup.mk' _
  have hπ : ∀ x : ↥M, π x = 1 ↔ (x : G) ∈ yOfL22 T M := fun x => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  intro w hw
  have hwU : w ∈ uOfL22 T M := Hyp1281Two.wOfU_le_uOfL22 T M hw
  have hwM : w ∈ M := h.inM.2 (h.uOfL22_le_T hwU)
  have hgM : g ∈ M := h.le hg.mem
  set w' : ↥M := ⟨w, hwM⟩ with hw'
  set g' : ↥M := ⟨g, hgM⟩ with hg'
  have hrel := (h.module_relations hU hg huU huW).1 w hw
  rw [hEV] at hrel
  have hrelL := hVL hrel
  have h1 : π (w' * (g' * w' * g'⁻¹) * (g' * g' * w' * (g' * g')⁻¹)) = 1 := (hπ _).mpr hrelL
  have hg1 : π g' = 1 := (hπ g').mpr hg.mem
  rw [map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_mul,
    hg1] at h1
  have hx3 : π w' * π w' * π w' = 1 := by simpa using h1
  have hx2 : π w' * π w' = 1 := by
    have : π (w' * w') = 1 := by
      refine (hπ _).mpr ?_
      have := h.sq_mem_omegaOneCenter hwU
      rw [sq] at this
      exact hVL (Hyp1281Two.omegaOneCenter_le_VZ T M this)
    simpa using this
  have hx1 : π w' = 1 := by
    have : π w' = π w' * π w' * π w' * (π w' * π w')⁻¹ := by group
    rw [this, hx3, hx2]; simp
  exact (hπ w').mp hx1

theorem pCoreOf_sup_le_yOfL22 :
    pCoreOf 2 (yOfL22 T M ⊔ uOfL22 T M) ≤ yOfL22 T M := by
  rw [(h.pCoreOf_sup_uOfL22_eq_wOfU_sup hU hg).1]
  refine sup_le (wOfU_le_yOfL22 h hU hg hEV) ?_
  intro y hy
  have hy' := wOfU_le_yOfL22 h hU hg hEV (mem_rconj.mp hy)
  have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg.mem) hy') hg.mem
  simpa [mul_assoc] using this

theorem r_eq_of : rOf T M = pCoreOf 2 (yOfL22 T M) := by
  unfold rOf
  rw [iTwo_eq h hU]
  apply le_antisymm
  · refine le_pCoreOf_of_le_normalizer 2 (pCoreOf_sup_le_yOfL22 h hU hg hEV) ?_
      (pCoreOf_isPGroup 2 _)
    exact le_sup_left.trans (le_normalizer_pCoreOf 2 _)
  · refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left) ?_
      (pCoreOf_isPGroup 2 _)
    refine sup_le (le_normalizer_pCoreOf 2 _) ?_
    exact (h.uOfL22_le_T.trans (h.inM.2.trans h.normal)).trans
      (normalizer_le_normalizer_pCoreOf 2 _)


omit hEV in
theorem pCoreOf_sup_le_normalizer_Z {c : G} (hc : c ∈ pCoreOf 2 (yOfL22 T M ⊔ uOfL22 T M)) :
    c ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
  rw [h.pCoreOf_sup_uOfL22_eq hU hg] at hc
  exact Subgroup.centralizer_le_normalizer _
    (Subgroup.centralizer_le (Hyp1281Two.omegaOneCenter_le_VZ T M) hc.2)

theorem good_of_order_three {x : G} (hx : x ∈ yOfL22 T M ⊔ uOfL22 T M) (hx3 : orderOf x = 3) :
    GoodElt128 T (yOfL22 T M) x := by
  have hgI : g ∈ yOfL22 T M ⊔ uOfL22 T M := Subgroup.mem_sup_left hg.mem
  have hgP : g ∈ yOfL22 T M ⊔ T := Subgroup.mem_sup_left hg.mem
  have hxP : x ∈ yOfL22 T M ⊔ T := h.sup_uOfL22_le_LT hx
  have hg3 : phiI h ⟨g, hgI⟩ ^ 3 = 1 := by
    rw [← map_pow, phiI_eq_one_iff]
    exact h.pow_three_mem_pCoreOf_LT hg.mem
  have hg1 : phiI h ⟨g, hgI⟩ ≠ 1 := fun he =>
    h.not_mem_pCoreOf_LT_of_goodElt hg ((phiI_eq_one_iff h _).mp he)
  have hx3' : phiI h ⟨x, hx⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hx⟩ : ↥(yOfL22 T M ⊔ uOfL22 T M)) ^ 3 = 1 := Subtype.ext (by
      simpa using (hx3 ▸ pow_orderOf_eq_one x))
    rw [this, map_one]
  have hx1 : phiI h ⟨x, hx⟩ ≠ 1 := by
    intro he
    have hmem := (phiI_eq_one_iff h _).mp he
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (yOfL22 T M ⊔ T)) ⟨x, hmem⟩
    have : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h2 := orderOf_dvd_of_pow_eq_one this
    rw [hx3] at h2
    have h3 : 3 ∣ 2 ^ k := h2
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have hker := ker_phiI h hU hg
  have hSL := pCoreOf_sup_le_yOfL22 h hU hg hEV
  rcases perm3_order_three _ _ hx3' hx1 hg3 hg1 with h1 | h1
  · have hc : (x * g⁻¹ : G) ∈ pCoreOf 2 (yOfL22 T M ⊔ uOfL22 T M) := by
      have h2 : phiI h (⟨x, hx⟩ * ⟨g, hgI⟩⁻¹) = 1 := by rw [map_mul, map_inv, h1]; simp
      have h3 : (⟨x, hx⟩ * ⟨g, hgI⟩⁻¹ : ↥(yOfL22 T M ⊔ uOfL22 T M)) ∈
          CFSG.Open.pCore 2 ↥(yOfL22 T M ⊔ uOfL22 T M) := hker ▸ h2
      exact (mem_pCore_iff _).mp h3
    refine ⟨?_, fun hxN => hg.not_mem ?_⟩
    · have := Subgroup.mul_mem _ (hSL hc) hg.mem
      simpa using this
    · have hcN := pCoreOf_sup_le_normalizer_Z h hU hg hc
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hcN) hxN
      simpa [mul_assoc] using this
  · have hc : (x * g : G) ∈ pCoreOf 2 (yOfL22 T M ⊔ uOfL22 T M) := by
      have h2 : phiI h (⟨x, hx⟩ * ⟨g, hgI⟩) = 1 := by rw [map_mul, h1]; simp
      have h3 : (⟨x, hx⟩ * ⟨g, hgI⟩ : ↥(yOfL22 T M ⊔ uOfL22 T M)) ∈
          CFSG.Open.pCore 2 ↥(yOfL22 T M ⊔ uOfL22 T M) := hker ▸ h2
      exact (mem_pCore_iff _).mp h3
    refine ⟨?_, fun hxN => hg.not_mem ?_⟩
    · have := Subgroup.mul_mem _ (hSL hc) (Subgroup.inv_mem _ hg.mem)
      simpa using this
    · have hcN := pCoreOf_sup_le_normalizer_Z h hU hg hc
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hxN) hcN
      have e : x⁻¹ * (x * g) = g := by group
      simpa [e] using this

theorem r_fpf_of : ∀ x ∈ iTwo T M, orderOf x = 3 → ∀ r ∈ rOf T M, x * r * x⁻¹ = r → r = 1 := by
  intro x hxI hx3 r hr hfix
  rw [iTwo_eq h hU] at hxI
  have hxg := good_of_order_three h hU hg hEV hxI hx3
  obtain ⟨u, huU, huW⟩ := exists_mem_U_not_mem_W h hU
  have hindep := wOfU_inf_rconj_indep h hU hg hxg
  have h4 := (h.module_relations hU hxg huU huW).2.2.2 r (by
    unfold rOf at hr
    rwa [iTwo_eq h hU] at hr) (by
    rw [hfix]; simp [hindep])
  rw [hindep, hEV] at h4
  exact eq_one_of_conj_eq_of_mem_VZ h hxg h4 hfix

end WInL

end S143

end CFSG.Quasithin
