module

public import CFSG.Quasithin.Vol2.KGFact1291S3Red
public import CFSG.Quasithin.Vol2.KGFact1297A7

public section

namespace CFSG.Quasithin.H13.KG1291S

open CFSG.Open CFSG.QuasithinUnique.Vol2Native.A312L.Seven Equiv Matrix

abbrev a7sig : P7 := perm7 [[0, 2], [1, 3]]

theorem D7_le_centralizer : D7 ≤ Subgroup.centralizer ({a7sig} : Set P7) := by
  rw [D7, Subgroup.closure_le]
  intro g hg
  simp only [dGens, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  rcases hg with rfl | rfl <;> decide

theorem a7g3_not_mem_normalizer : KG1297.a7g3 ∉ Subgroup.normalizer (D7 : Set P7) := by
  intro h
  have hd : KG1297.a7d2 ∈ D7 := Subgroup.subset_closure (by simp [dGens])
  have hmem := (Subgroup.mem_normalizer_iff.1 h KG1297.a7d2).1 hd
  have := D7_le_centralizer hmem
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  revert this
  decide

theorem D7_le_Z3 : D7 ≤ Z 3 := D7_le_closure [perm7 [[2, 3], [4, 5]]]

theorem Z3_le_A7s : Z 3 ≤ A7s := by
  rw [Z, Subgroup.closure_le]
  intro g hg
  have hg' : g ∈ dGens ++ [perm7 [[2, 3], [4, 5]]] := by simpa [latGens] using hg
  rcases List.mem_append.mp hg' with h | h
  · exact D7_le_A7s (Subgroup.subset_closure h)
  · rw [List.mem_singleton.mp h]
    exact Equiv.Perm.mem_alternatingGroup.mpr (by decide)

theorem s3Hyp_A7
    {B : Subgroup ↥(alternatingGroup (Fin 7))}
    (hB : Nonempty (ModO2 B ≃* SpecialLinearGroup (Fin 3) (ZMod 2))) : S3Hyp B := by
  intro T Y hTY hBY hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card B = 168 := (KG1296.pCoreOf_eq_bot_of_A7 hB).2
  obtain ⟨-, hT2, hTodd⟩ := isSylowTwoOf_T7
  have hTodd' : ¬ 2 ∣ T7.index := by
    rwa [← Subgroup.relIndex_top_right]
  set T₇ : Sylow 2 ↥(alternatingGroup (Fin 7)) := hT2.toSylow hTodd' with hT₇
  obtain ⟨g, -, hg⟩ := KG1297.exists_conj_sylow (P := ⊤) T T₇ le_top le_top
  set c := MulAut.conj g with hc
  have hinj : Function.Injective (c.toMonoidHom : _ → _) := c.injective
  have hsurj : Function.Surjective (c.toMonoidHom : _ → _) := c.surjective
  have hTc : (T : Subgroup ↥(alternatingGroup (Fin 7))).map c.toMonoidHom = T7 := by
    rw [hg]
    rfl
  set Y' := Y.map c.toMonoidHom with hY'def
  have hTY' : T7 ≤ Y' := hTc ▸ Subgroup.map_mono hTY
  have hBY' : B.map c.toMonoidHom ≤ Y' := Subgroup.map_mono hBY
  have hY' : Y' ≠ ⊤ := by
    intro htop
    apply hY
    have := congrArg (Subgroup.comap c.toMonoidHom) htop
    rwa [hY'def, Subgroup.comap_map_eq_self_of_injective hinj, Subgroup.comap_top] at this
  have hdvd : 168 ∣ Nat.card Y' := by
    have := Subgroup.card_dvd_of_le hBY'
    rwa [Subgroup.card_map_of_injective hinj, hcard] at this
  have h168 : Nat.card Y' = 168 := by
    by_contra hne
    exact hY' (KG1297.eq_top_of_dvd hTY' hdvd hne)
  obtain ⟨k, hk, hYk⟩ := overgroup_Z hTY'
  have hk89 : k = 8 ∨ k = 9 := by
    have hcardk := card_Z hk
    rw [← hYk, card_map_subtype, h168] at hcardk
    interval_cases k <;> simp only [List.getD_cons_succ, List.getD_cons_zero] at hcardk <;> omega
  set H' : Subgroup ↥(alternatingGroup (Fin 7)) := (Z 3).comap A7s.subtype with hH'def
  have hH'map : H'.map A7s.subtype = Z 3 := by
    rw [hH'def, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_eq_right.mpr Z3_le_A7s]
  have hTH' : T7 ≤ H' := by
    intro t ht
    exact D7_le_Z3 (Subgroup.mem_subgroupOf.mp ht)
  have hg3Z : KG1297.a7g3 ∈ Z 3 := KG1297.mem_Z_of_mem_gens (by simp [latGens])
  have hg3A : KG1297.a7g3 ∈ A7s := Z3_le_A7s hg3Z
  have hg3H : (⟨KG1297.a7g3, hg3A⟩ : ↥A7s) ∈ H' := hg3Z
  have hHY' : ¬ H' ≤ Y' := by
    intro hle
    have h1 : KG1297.a7g3 ∈ Y'.map A7s.subtype := ⟨_, hle hg3H, rfl⟩
    rw [hYk] at h1
    exact KG1297.not_mem_Z89 hk89 h1
  have hmod : Nonempty (ModO2 H' ≃* Equiv.Perm (Fin 3)) := by
    refine modO2_perm3_of_index_three hTH' hT2 ?_ ?_
    · have hH'card : Nat.card H' = 24 := by
        rw [← card_map_subtype, hH'map, card_Z (by norm_num : 3 < 12)]
        rfl
      have hTcard : Nat.card T7 = 8 := by
        rw [T7, Nat.card_congr (Subgroup.subgroupOfEquivOfLe D7_le_A7s).toEquiv, card_D7]
      have h1 := (T7.subgroupOf H').card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH').toEquiv, hTcard, hH'card] at h1
      show (T7.subgroupOf H').index = 3
      omega
    · intro hle
      apply a7g3_not_mem_normalizer
      rw [Subgroup.mem_normalizer_iff]
      intro d
      constructor
      · intro hd
        have hdA : d ∈ A7s := D7_le_A7s hd
        have hdT : (⟨d, hdA⟩ : ↥A7s) ∈ T7 := Subgroup.mem_subgroupOf.mpr hd
        have := (Subgroup.mem_normalizer_iff.1 (hle hg3H) _).1 hdT
        exact Subgroup.mem_subgroupOf.mp this
      · intro hd
        have hdA' : KG1297.a7g3 * d * KG1297.a7g3⁻¹ ∈ A7s := D7_le_A7s hd
        have hdA : d ∈ A7s := by
          have := A7s.mul_mem (A7s.mul_mem (A7s.inv_mem hg3A) hdA') hg3A
          simpa [mul_assoc] using this
        have hdT : (⟨KG1297.a7g3, hg3A⟩ * ⟨d, hdA⟩ * (⟨KG1297.a7g3, hg3A⟩ : ↥A7s)⁻¹ : ↥A7s) ∈
            T7 := Subgroup.mem_subgroupOf.mpr hd
        exact Subgroup.mem_subgroupOf.mp
          ((Subgroup.mem_normalizer_iff.1 (hle hg3H) ⟨d, hdA⟩).2 hdT)
  have hHH : (H'.comap c.toMonoidHom).map c.toMonoidHom = H' :=
    Subgroup.map_comap_eq_self_of_surjective hsurj H'
  refine ⟨H'.comap c.toMonoidHom, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_le_iff_le_comap, hTc]
    exact hTH'
  · intro hle
    apply hHY'
    rw [← hHH]
    exact Subgroup.map_mono hle
  · obtain ⟨e'⟩ := KG1296.nonempty_modO2_map c (H'.comap c.toMonoidHom)
    rw [hHH] at e'
    obtain ⟨eH⟩ := hmod
    exact ⟨e'.trans eH⟩

end CFSG.Quasithin.H13.KG1291S
