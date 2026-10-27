module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitRaw
import CFSG.LocalAnalysis.StandardType.GGQ2UnitCutThree
import CFSG.LocalAnalysis.StandardType.GGQ2UnitHeartCutThree

public section

namespace CFSG.StandardType.GGQ2Frame.UnitRaw

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose] def unitVec (N : ℕ) (a : Fin N) : Vfull N := (oneLine N).mkQ (Pi.single a 1)

@[expose] def LineShapes : Prop :=
  ∀ (N : ℕ) (v : Vfull N) (S : Finset (Fin N)), v ≠ 0 → occurs (Submodule.span F {v}) S →
    cent S = Submodule.span F {v} →
      ∃ (a : Fin N) (s : F), s ≠ 0 ∧ v = s • unitVec N a ∧ S = Finset.univ.erase a

@[expose] def PlaneShapes : Prop :=
  ∀ (N : ℕ) (U : Submodule F (Vfull N)) (S : Finset (Fin N)), finrank F U = 2 →
    occurs U S → cent S = U →
      ∃ a b : Fin N, a ≠ b ∧ S = Finset.univ \ {a, b} ∧
        U = Submodule.span F {unitVec N a, unitVec N b}

end

private theorem gcus_unitVec_mem_cent {N : ℕ} {S : Finset (Fin N)} {a : Fin N} (ha : a ∉ S) :
    unitVec N a ∈ cent S := by
  rw [mem_cent_iff]
  refine ⟨Pi.single a (1 : F), rfl, fun i hi j hj => ?_⟩
  have hia : i ≠ a := fun h => ha (h ▸ hi)
  have hja : j ≠ a := fun h => ha (h ▸ hj)
  rw [Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hja]

private theorem gcus_sub_unitVec_mem_cent {N : ℕ} {S : Finset (Fin N)} {a b : Fin N}
    (ha : a ∉ S) (hb : b ∉ S) : unitVec N a - unitVec N b ∈ cent S :=
  Submodule.sub_mem _ (gcus_unitVec_mem_cent ha) (gcus_unitVec_mem_cent hb)

private theorem gcus_sub_unitVec_mem_heart {N : ℕ} (a b : Fin N) :
    unitVec N a - unitVec N b ∈ heart N := by
  have hsingle : ∀ c : Fin N, sumFun N (Pi.single c (1 : F)) = 1 := by
    intro c
    rw [sumFun_apply, Finset.sum_pi_single']
    simp
  have hker : Pi.single a (1 : F) - Pi.single b (1 : F) ∈ LinearMap.ker (sumFun N) := by
    rw [LinearMap.mem_ker, map_sub, hsingle a, hsingle b, sub_self]
  rw [heart, Submodule.mem_map]
  exact ⟨_, hker, by rw [map_sub, unitVec, unitVec]⟩

private theorem gcus_diffFun_unitVec_self {N : ℕ} {j a : Fin N} (hja : j ≠ a) :
    diffFun N a j (unitVec N a) = 1 := by
  rw [unitVec, diffFun_mk, Pi.single_eq_same, Pi.single_eq_of_ne hja, sub_zero]

private theorem gcus_diffFun_unitVec_ne_ne {N : ℕ} {i j a : Fin N} (hia : i ≠ a) (hja : j ≠ a) :
    diffFun N i j (unitVec N a) = 0 := by
  rw [unitVec, diffFun_mk, Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hja, sub_self]

private theorem gcus_compl_card_eq {N : ℕ} {S : Finset (Fin N)} {r : ℕ}
    (h : N - S.card = r) : Sᶜ.card = r := by
  rw [Finset.card_compl, Fintype.card_fin]
  exact h

private theorem gcus_eq_erase_of_compl_card_one {N : ℕ} {S : Finset (Fin N)}
    (h : Sᶜ.card = 1) : ∃ a : Fin N, S = Finset.univ.erase a := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hSS : S = (Sᶜ)ᶜ := by ext i; simp
  refine ⟨a, ?_⟩
  rw [hSS, ha, Finset.compl_eq_univ_sdiff, Finset.sdiff_singleton_eq_erase]

private theorem gcus_eq_sdiff_pair_of_compl_card_two {N : ℕ} {S : Finset (Fin N)}
    (h : Sᶜ.card = 2) : ∃ a b : Fin N, a ≠ b ∧ S = Finset.univ \ {a, b} := by
  obtain ⟨a, b, hab, ha⟩ := Finset.card_eq_two.mp h
  have hSS : S = (Sᶜ)ᶜ := by ext i; simp
  refine ⟨a, b, hab, ?_⟩
  rw [hSS, ha, Finset.compl_eq_univ_sdiff]

private theorem gcus_eq_sdiff_triple_of_compl_card_three {N : ℕ} {S : Finset (Fin N)}
    (h : Sᶜ.card = 3) :
    ∃ a b c : Fin N, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ S = Finset.univ \ {a, b, c} := by
  obtain ⟨a, b, c, hab, hac, hbc, ha⟩ := Finset.card_eq_three.mp h
  have hSS : S = (Sᶜ)ᶜ := by ext i; simp
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  rw [hSS, ha, Finset.compl_eq_univ_sdiff]

private theorem gcus_centH_univ {N : ℕ} :
    centH (Finset.univ : Finset (Fin N)) = ⊥ := by
  rw [centH, cent_univ, Submodule.comap_bot,
    LinearMap.ker_eq_bot_of_injective (heart N).subtype_injective]

private theorem gcus_eq_smul_unitVec_of_mem_span {N : ℕ} {v : Vfull N} {a : Fin N}
    (hmem : unitVec N a ∈ Submodule.span F {v}) (hu : unitVec N a ≠ 0) :
    ∃ s : F, s ≠ 0 ∧ v = s • unitVec N a := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at hc
    exact hu hc.symm
  refine ⟨c⁻¹, inv_ne_zero hc0, ?_⟩
  rw [← hc, inv_smul_smul₀ hc0 v]

private theorem gcus_sub_unitVec_mem_centH {N : ℕ} {S : Finset (Fin N)} {a b : Fin N}
    (ha : a ∉ S) (hb : b ∉ S) :
    (⟨unitVec N a - unitVec N b, gcus_sub_unitVec_mem_heart a b⟩ : ↥(heart N)) ∈ centH S :=
  (mem_centH_iff S _).mpr (gcus_sub_unitVec_mem_cent ha hb)

theorem lineShapes_holds : LineShapes := by
  intro N v S hv hocc hcent
  have hSne : S.Nonempty := hocc.1
  have hSuniv : S ≠ Finset.univ := by
    intro h
    have hbot : Submodule.span F {v} = ⊥ := by rw [← hcent, h, cent_univ]
    exact hv (Submodule.span_singleton_eq_bot.mp hbot)
  have hdim : finrank F (cent S) = N - S.card := finrank_cent S hSne hSuniv
  have hNS : N - S.card = 1 := by rw [← hdim, hcent, finrank_span_singleton hv]
  obtain ⟨a, hS⟩ := gcus_eq_erase_of_compl_card_one (gcus_compl_card_eq hNS)
  have haS : a ∉ S := by rw [hS]; simp
  have hmem : unitVec N a ∈ Submodule.span F {v} := hcent ▸ gcus_unitVec_mem_cent haS
  obtain ⟨i, hi⟩ := hSne
  have hia : i ≠ a := by
    rw [hS] at hi
    exact (Finset.mem_erase.mp hi).1
  have hu : unitVec N a ≠ 0 := by
    intro h0
    have h1 : diffFun N a i (unitVec N a) = 0 := by rw [h0, map_zero]
    rw [gcus_diffFun_unitVec_self hia] at h1
    exact one_ne_zero h1
  obtain ⟨s, hs0, hsv⟩ := gcus_eq_smul_unitVec_of_mem_span hmem hu
  exact ⟨a, s, hs0, hsv, hS⟩

theorem planeShapes_holds : PlaneShapes := by
  intro N U S hU hocc hcent
  have hSne : S.Nonempty := hocc.1
  have hSuniv : S ≠ Finset.univ := by
    intro h
    have hUbot : U = ⊥ := by rw [← hcent, h, cent_univ]
    rw [hUbot, finrank_bot] at hU
    omega
  have hdim : finrank F (cent S) = N - S.card := finrank_cent S hSne hSuniv
  have hNS : N - S.card = 2 := by rw [← hdim, hcent, hU]
  obtain ⟨a, b, hab, hS⟩ :=
    gcus_eq_sdiff_pair_of_compl_card_two (gcus_compl_card_eq hNS)
  have haS : a ∉ S := by rw [hS]; simp
  have hbS : b ∉ S := by rw [hS]; simp
  have hle : Submodule.span F ({unitVec N a, unitVec N b} : Set (Vfull N)) ≤ U := by
    rw [Submodule.span_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact hcent ▸ gcus_unitVec_mem_cent haS
    · exact hcent ▸ gcus_unitVec_mem_cent hbS
  obtain ⟨i, hi⟩ := hSne
  rw [hS] at hi
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ,
    true_and, not_or] at hi
  obtain ⟨hia, hib⟩ := hi
  have hind : LinearIndependent F ![unitVec N a, unitVec N b] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hs : s = 0 := by
      have h1 : diffFun N a i (s • unitVec N a + t • unitVec N b) = 0 := by rw [hst, map_zero]
      rw [map_add, map_smul, map_smul, gcus_diffFun_unitVec_self hia,
        gcus_diffFun_unitVec_ne_ne hab hib] at h1
      simpa using h1
    refine ⟨hs, ?_⟩
    have h2 : diffFun N b i (s • unitVec N a + t • unitVec N b) = 0 := by rw [hst, map_zero]
    rw [map_add, map_smul, map_smul, gcus_diffFun_unitVec_ne_ne (Ne.symm hab) hia,
      gcus_diffFun_unitVec_self hib, hs] at h2
    simpa using h2
  have hfin : finrank F (Submodule.span F ({unitVec N a, unitVec N b} : Set (Vfull N))) = 2 := by
    have hrange : Set.range ![unitVec N a, unitVec N b] =
        ({unitVec N a, unitVec N b} : Set (Vfull N)) := by
      ext z
      constructor
      · rintro ⟨k, rfl⟩
        fin_cases k <;> simp
      · intro hz
        rcases hz with rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [← hrange, finrank_span_eq_card hind, Fintype.card_fin]
  have hEq : Submodule.span F ({unitVec N a, unitVec N b} : Set (Vfull N)) = U :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, hU])
  exact ⟨a, b, hab, hS, hEq.symm⟩

theorem heartLineShapes_holds :
    ∀ (N : ℕ), 3 ∣ N → ∀ (v : ↥(heart N)) (S : Finset (Fin N)), v ≠ 0 →
      occursH (Submodule.span F {v}) S → centH S = Submodule.span F {v} →
        ∃ (a b : Fin N) (s : F), a ≠ b ∧ s ≠ 0 ∧
          (v : Vfull N) = s • (unitVec N a - unitVec N b) ∧ S = Finset.univ \ {a, b} := by
  intro N h3 v S hv hocc hcent
  have hSne : S.Nonempty := hocc.1
  have hSuniv : S ≠ Finset.univ := by
    intro h
    have hbot : Submodule.span F {v} = ⊥ := by rw [← hcent, h, gcus_centH_univ]
    exact hv (Submodule.span_singleton_eq_bot.mp hbot)
  have hdim : finrank F (centH S) = N - S.card - 1 := finrank_centH h3 S hSne hSuniv
  have hdim1 : N - S.card - 1 = 1 := by rw [← hdim, hcent, finrank_span_singleton hv]
  have hNS : N - S.card = 2 := by
    have hcle : S.card ≤ N := by simpa [Fintype.card_fin] using Finset.card_le_univ S
    omega
  obtain ⟨a, b, hab, hS⟩ :=
    gcus_eq_sdiff_pair_of_compl_card_two (gcus_compl_card_eq hNS)
  have haS : a ∉ S := by rw [hS]; simp
  have hbS : b ∉ S := by rw [hS]; simp
  let d : ↥(heart N) := ⟨unitVec N a - unitVec N b, gcus_sub_unitVec_mem_heart a b⟩
  have hdcent : d ∈ centH S := gcus_sub_unitVec_mem_centH haS hbS
  have hmem : d ∈ Submodule.span F {v} := hcent ▸ hdcent
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hcval : c • (v : Vfull N) = unitVec N a - unitVec N b := by
    have h := congrArg (fun x : ↥(heart N) => (x : Vfull N)) hc
    simpa using h
  obtain ⟨i, hi⟩ := hSne
  rw [hS] at hi
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ,
    true_and, not_or] at hi
  obtain ⟨hia, hib⟩ := hi
  have hval1 : diffFun N a i (unitVec N a - unitVec N b) = 1 := by
    rw [map_sub, gcus_diffFun_unitVec_self hia, gcus_diffFun_unitVec_ne_ne hab hib, sub_zero]
  have hne : d ≠ 0 := by
    intro h0
    have h1 : diffFun N a i (d : Vfull N) = 0 := by rw [h0]; simp
    have h2 : diffFun N a i (d : Vfull N) = 1 := by
      change diffFun N a i (unitVec N a - unitVec N b) = 1
      exact hval1
    rw [h2] at h1
    exact one_ne_zero h1
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at hc
    exact hne hc.symm
  refine ⟨a, b, c⁻¹, hab, inv_ne_zero hc0, ?_, hS⟩
  rw [← hcval]
  exact (inv_smul_smul₀ hc0 (v : Vfull N)).symm

theorem heartPlaneShapes_holds :
    ∀ (N : ℕ), 3 ∣ N → ∀ (U : Submodule F ↥(heart N)) (S : Finset (Fin N)), finrank F U = 2 →
      occursH U S → centH S = U →
        ∃ a b c : Fin N, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ S = Finset.univ \ {a, b, c} ∧
          U.map (heart N).subtype =
            Submodule.span F {unitVec N a - unitVec N b, unitVec N b - unitVec N c} := by
  intro N h3 U S hU hocc hcent
  have hSne : S.Nonempty := hocc.1
  have hSuniv : S ≠ Finset.univ := by
    intro h
    have hUbot : U = ⊥ := by rw [← hcent, h, gcus_centH_univ]
    rw [hUbot, finrank_bot] at hU
    omega
  have hdim : finrank F (centH S) = N - S.card - 1 := finrank_centH h3 S hSne hSuniv
  have hdim2 : N - S.card - 1 = 2 := by rw [← hdim, hcent, hU]
  have hNS : N - S.card = 3 := by
    have hcle : S.card ≤ N := by simpa [Fintype.card_fin] using Finset.card_le_univ S
    omega
  obtain ⟨a, b, c, hab, hac, hbc, hS⟩ :=
    gcus_eq_sdiff_triple_of_compl_card_three (gcus_compl_card_eq hNS)
  have haS : a ∉ S := by rw [hS]; simp
  have hbS : b ∉ S := by rw [hS]; simp
  have hcS : c ∉ S := by rw [hS]; simp
  set x : Vfull N := unitVec N a - unitVec N b with hx
  set y : Vfull N := unitVec N b - unitVec N c with hy
  have hxheart : x ∈ heart N := by rw [hx]; exact gcus_sub_unitVec_mem_heart a b
  have hyheart : y ∈ heart N := by rw [hy]; exact gcus_sub_unitVec_mem_heart b c
  have hxcent : x ∈ cent S := by rw [hx]; exact gcus_sub_unitVec_mem_cent haS hbS
  have hycent : y ∈ cent S := by rw [hy]; exact gcus_sub_unitVec_mem_cent hbS hcS
  have hxU : x ∈ U.map (heart N).subtype := by
    rw [Submodule.mem_map]
    refine ⟨⟨x, hxheart⟩, ?_, rfl⟩
    rw [← hcent]
    exact (mem_centH_iff S _).mpr hxcent
  have hyU : y ∈ U.map (heart N).subtype := by
    rw [Submodule.mem_map]
    refine ⟨⟨y, hyheart⟩, ?_, rfl⟩
    rw [← hcent]
    exact (mem_centH_iff S _).mpr hycent
  have hPle : Submodule.span F ({x, y} : Set (Vfull N)) ≤ U.map (heart N).subtype := by
    rw [Submodule.span_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact hxU
    · exact hyU
  obtain ⟨i, hi⟩ := hSne
  rw [hS] at hi
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ,
    true_and, not_or] at hi
  obtain ⟨hia, hib, hic⟩ := hi
  have hx1 : diffFun N a i x = 1 := by
    rw [hx, map_sub, gcus_diffFun_unitVec_self hia, gcus_diffFun_unitVec_ne_ne hab hib, sub_zero]
  have hy1 : diffFun N a i y = 0 := by
    rw [hy, map_sub, gcus_diffFun_unitVec_ne_ne hab hib, gcus_diffFun_unitVec_ne_ne hac hic,
      sub_self]
  have hx2 : diffFun N c i x = 0 := by
    rw [hx, map_sub, gcus_diffFun_unitVec_ne_ne (Ne.symm hac) hia,
      gcus_diffFun_unitVec_ne_ne (Ne.symm hbc) hib, sub_self]
  have hy2 : diffFun N c i y = -1 := by
    rw [hy, map_sub, gcus_diffFun_unitVec_ne_ne (Ne.symm hbc) hib,
      gcus_diffFun_unitVec_self hic, zero_sub]
  have hind : LinearIndependent F ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hs : s = 0 := by
      have h1 : diffFun N a i (s • x + t • y) = 0 := by rw [hst, map_zero]
      rw [map_add, map_smul, map_smul, hx1, hy1] at h1
      simpa using h1
    refine ⟨hs, ?_⟩
    have h2 : diffFun N c i (s • x + t • y) = 0 := by rw [hst, map_zero]
    rw [map_add, map_smul, map_smul, hx2, hy2, hs] at h2
    simpa using h2
  have hPfin : finrank F (Submodule.span F ({x, y} : Set (Vfull N))) = 2 := by
    have hrange : Set.range ![x, y] = ({x, y} : Set (Vfull N)) := by
      ext z
      constructor
      · rintro ⟨k, rfl⟩
        fin_cases k <;> simp
      · intro hz
        rcases hz with rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [← hrange, finrank_span_eq_card hind, Fintype.card_fin]
  have hmapfin : finrank F (U.map (heart N).subtype) = 2 := by
    rw [Submodule.finrank_map_subtype_eq, hU]
  have hEq : Submodule.span F ({x, y} : Set (Vfull N)) = U.map (heart N).subtype :=
    Submodule.eq_of_le_of_finrank_eq hPle (by rw [hPfin, hmapfin])
  refine ⟨a, b, c, hab, hac, hbc, hS, ?_⟩
  simpa [hx, hy] using hEq.symm

end CFSG.StandardType.GGQ2Frame.UnitRaw
