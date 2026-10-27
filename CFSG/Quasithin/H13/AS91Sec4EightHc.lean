module

public import CFSG.Quasithin.Vol2.Asc94.TSModel1b
public import CFSG.Quasithin.Vol2.Asc94.TSModel2
public import CFSG.Quasithin.Vol2.Asc94.TSF6Model
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.Quasithin.H13.AS91.HcFacts

open Subgroup CFSG.Open CFSG.Quasithin.A94 CFSG.Quasithin.A94.L52

theorem zt_inv : zt⁻¹ = zt :=
  inv_eq_of_mul_eq_one_right (by have := zt_sq; rw [sq] at this; exact this)

theorem zt_mem_U1 : zt ∈ U1 := (Subgroup.mem_inf.mp zt_mem_inf).1

theorem U1_le_of_normal {K : Subgroup Hc} (hK : K.Normal) {x : Hc} (hxK : x ∈ K) (hxU : x ∈ U1)
    (hx1 : x ≠ 1) (hxz : x ≠ zt) : U1 ≤ K := by
  have hconj : ∀ {y : Hc}, y ∈ U1 → y ≠ 1 → y ≠ zt → y ∈ K := by
    intro y hy hy1 hyz
    obtain ⟨g, hg⟩ := U1_trans hxU hx1 hxz hy hy1 hyz
    rw [hg]
    have := hK.conj_mem x hxK g⁻¹
    rwa [inv_inv] at this
  intro y hy
  by_cases hy1 : y = 1
  · rw [hy1]
    exact one_mem _
  by_cases hyz : y = zt
  · have hxzU : x * zt ∈ U1 := mul_mem hxU zt_mem_U1
    have h1 : x * zt ≠ 1 := fun h => hxz (by
      have := eq_inv_of_mul_eq_one_left h
      rw [zt_inv] at this
      exact this)
    have h2 : x * zt ≠ zt := fun h => hx1 (by simpa using h)
    have hm := mul_mem (inv_mem hxK) (hconj hxzU h1 h2)
    rw [hyz]
    simpa using hm
  · exact hconj hy hy1 hyz

theorem U2_le_of_normal {K : Subgroup Hc} (hK : K.Normal) {x : Hc} (hxK : x ∈ K) (hxU : x ∈ U2)
    (hx1 : x ≠ 1) (hxz : x ≠ zt) : U2 ≤ K := by
  have hsurj : Function.Surjective sigmaHom := fun y => ⟨sigmaHom y, sigmaHom_sigmaHom y⟩
  have hK2 : (K.map sigmaHom).Normal := hK.map sigmaHom hsurj
  have h1 := U1_le_of_normal hK2 (x := sigma x) ⟨x, hxK, rfl⟩ (sigma_U2 hxU)
    (fun h => hx1 (by rw [← sigma_sigma x, h, map_one]))
    (fun h => hxz (by rw [← sigma_sigma x, h, sigma_zt]))
  intro y hy
  have h2 := h1 (sigma_U2 hy)
  obtain ⟨y', hy', hy'y⟩ := h2
  have : y' = y := by
    have := congrArg sigmaHom hy'y
    rwa [sigmaHom_sigmaHom, show sigmaHom (sigma y) = y from sigmaHom_sigmaHom y] at this
  rwa [← this]

theorem unipS_ne_one {i j : Fin 5} (hij : i < j) : unipS i j hij 1 ≠ 1 := by
  intro h
  have hc := congrArg (fun x : Hc => cm x i j) h
  simp only [cm_unipS, Matrix.add_apply, Matrix.single_apply_same, cm_one] at hc
  rw [Matrix.one_apply_ne (ne_of_lt hij)] at hc
  exact absurd hc (by decide)

theorem unipS_ne_zt {i j : Fin 5} (hij : i < j) (hne : (i, j) ≠ (0, 4)) :
    unipS i j hij 1 ≠ zt := by
  intro h
  have hc := congrArg (fun x : Hc => cm x i j) h
  have hne' : ¬ (0 = i ∧ 4 = j) := fun h' => hne (by rw [← h'.1, ← h'.2])
  simp only [cm_unipS, cm_zt, tt] at hc
  revert hc
  simp [Matrix.single_apply, hne', Matrix.one_apply_ne (ne_of_lt hij)]

theorem eq_top_of_A1_le {K : Subgroup Hc} (hK : K.Normal) (hA : A1 ≤ K) : K = ⊤ := by
  have hU1 : U1 ≤ K := U1_le_of_normal hK (hA (Subgroup.mem_inf.mp e02_mem).1)
    (Subgroup.mem_inf.mp e02_mem).2 (unipS_ne_one _) (unipS_ne_zt _ (by decide))
  have h14A : unipS 1 4 (by decide) 1 ∈ A1 := unipS_mem_patSub hSA _ 1 ⟨by decide, by decide⟩
  have h14U : unipS 1 4 (by decide) 1 ∈ U2 := unipS_mem_patSub hS2 _ 1 ⟨rfl, by decide⟩
  have hU2 : U2 ≤ K := U2_le_of_normal hK (hA h14A) h14U (unipS_ne_one _)
    (unipS_ne_zt _ (by decide))
  have hQ : Qh ≤ K := by
    intro x hx
    have hx' : x ∈ (Qh : Set Hc) := hx
    rw [Qh_eq_U1_mul_U2] at hx'
    obtain ⟨u, hu, v, hv, rfl⟩ := hx'
    exact mul_mem (hU1 hu) (hU2 hv)
  have hpi : K.map piHom = ⊤ := by
    haveI := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
    haveI := hK.map piHom piHom_surjective
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map piHom) with h | h
    · exfalso
      have h12A : unipS 1 2 (by decide) 1 ∈ A1 := unipS_mem_patSub hSA _ 1 ⟨by decide, by decide⟩
      have hmem : piHom (unipS 1 2 (by decide) 1) ∈ K.map piHom := ⟨_, hA h12A, rfl⟩
      rw [h, mem_bot] at hmem
      have hQ12 : unipS 1 2 (by decide) 1 ∈ Qh := MonoidHom.mem_ker.mpr hmem
      have := (mem_Qh_iff _).mp hQ12 1 2 (by decide)
      revert this
      simp only [cm_unipS, add_sub_cancel_left]
      decide
    · exact h
  rw [eq_top_iff]
  intro x _
  have hx : piHom x ∈ K.map piHom := by rw [hpi]; trivial
  obtain ⟨k, hk, hkx⟩ := hx
  have hkQ : k⁻¹ * x ∈ Qh := MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hkx, inv_mul_cancel])
  have := mul_mem hk (hQ hkQ)
  simpa using this

theorem eq_top_of_A2_le {K : Subgroup Hc} (hK : K.Normal) (hA : A2 ≤ K) : K = ⊤ := by
  have hsurj : Function.Surjective sigmaHom := fun y => ⟨sigmaHom y, sigmaHom_sigmaHom y⟩
  have h1 : K.map sigmaHom = ⊤ := eq_top_of_A1_le (hK.map sigmaHom hsurj) (by
    rw [← map_sigma_A2]
    exact Subgroup.map_mono hA)
  rw [eq_top_iff]
  intro x _
  have hx : sigmaHom x ∈ K.map sigmaHom := by rw [h1]; trivial
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := by
    have := congrArg sigmaHom hyx
    rwa [sigmaHom_sigmaHom, sigmaHom_sigmaHom] at this
  rwa [← this]

theorem eq_top_of_E64_le {K : Subgroup Hc} (hK : K.Normal) {X : Subgroup Hc}
    (hX : IsElemAbelian 2 X) (hXc : Nat.card X = 64) (hXK : X ≤ K) : K = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXp : IsPGroup 2 X := IsPGroup.of_card (n := 6) (by rw [hXc]; norm_num)
  obtain ⟨P, hXP⟩ := hXp.exists_le_sylow
  have hfac : (Nat.card Hc).factorization 2 = 10 := by
    rw [card_Hc, show (21504 : ℕ) = 2 ^ 10 * 21 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd]
  let T : Sylow 2 Hc := Sylow.ofCard Tm (by rw [card_Tm, hfac])
  have hT : (T : Subgroup Hc) = Tm := Sylow.coe_ofCard _ _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Hc P T
  obtain ⟨Y, hYdef⟩ : ∃ Y : Subgroup Hc, Y = X.map (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
  have hYT : Y ≤ Tm := by
    rw [hYdef, ← hT, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact Subgroup.map_mono hXP
  have hYab : IsElemAbelian 2 Y := by
    subst hYdef
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      change (a : Hc) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      exact congrArg _ (congrArg Subtype.val (hX.1.is_comm.comm (⟨a', ha'⟩ : X) ⟨b', hb'⟩))
    · obtain ⟨y', hy', rfl⟩ := hy
      rw [← map_pow, hX.2 y' hy', map_one]
  have hYcard : Nat.card Y = 64 := by
    rw [hYdef, Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective, hXc]
  have hYK : Y ≤ K := by
    rw [hYdef]
    rintro _ ⟨x, hx, rfl⟩
    exact hK.conj_mem x (hXK hx) g
  rcases f6Model_holds Y hYT hYab hYcard with h | h
  · exact eq_top_of_A1_le hK (h ▸ hYK)
  · exact eq_top_of_A2_le hK (h ▸ hYK)

end CFSG.Quasithin.H13.AS91.HcFacts
