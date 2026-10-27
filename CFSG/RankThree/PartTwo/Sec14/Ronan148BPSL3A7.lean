module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSA7
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSL3Gen

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts.KP2
open Equiv

namespace A7

theorem gen_of_nine {P : Subgroup (alternatingGroup (Fin 7))} (hP9 : Nat.card P = 9) :
    sSup {Y : Subgroup (alternatingGroup (Fin 7)) | ¬ 3 ∣ Nat.card Y ∧
      P ≤ Subgroup.normalizer (Y : Set (alternatingGroup (Fin 7)))} = ⊤ := by
  obtain ⟨x, hx⟩ := exists_conj hP9
  set c := MulAut.conj x with hc
  set P' := P.map c.toMonoidHom with hP'
  have h1 := mem_signalizers hx vOne_le_alt card_vOne
    (by
      rintro _ ⟨i, j, rfl⟩ _ ⟨m, rfl⟩
      obtain ⟨m', hm'⟩ := eNine_conj_vOne i j m
      exact ⟨m', hm'⟩) vOne_eq_commutator
  have h2 := mem_signalizers hx vTwo_le_alt card_vTwo
    (by
      rintro _ ⟨i, j, rfl⟩ _ ⟨m, rfl⟩
      obtain ⟨m', hm'⟩ := eNine_conj_vTwo i j m
      exact ⟨m', hm'⟩) vTwo_eq_commutator
  have htop : vOne.comap ι ⊔ vTwo.comap ι = ⊤ := by
    have hsup : (vOne.comap ι ⊔ vTwo.comap ι).map ι = vOne ⊔ vTwo := by
      rw [Subgroup.map_sup, Subgroup.map_comap_eq_self (by rw [range_ι]; exact vOne_le_alt),
        Subgroup.map_comap_eq_self (by rw [range_ι]; exact vTwo_le_alt)]
    rw [eq_top_iff]
    intro y _
    have hy : ι y ∈ vOne ⊔ vTwo := alt_le_vOne_sup_vTwo y.2
    rw [← hsup] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    rwa [← ι_injective hzy]
  have hmem : ∀ V : Subgroup (alternatingGroup (Fin 7)),
      V ∈ invariantPiSubgroups ⊤ P' (piCompl 3) →
      V.map c.symm.toMonoidHom ∈ {Y : Subgroup (alternatingGroup (Fin 7)) | ¬ 3 ∣ Nat.card Y ∧
        P ≤ Subgroup.normalizer (Y : Set (alternatingGroup (Fin 7)))} := by
    intro V hV
    rw [mem_invariantPiSubgroups_iff, isPiSubgroup_piCompl_iff Nat.prime_three] at hV
    refine ⟨by rw [Subgroup.card_map_of_injective c.symm.injective]; exact hV.2.1, ?_⟩
    rw [← Subgroup.map_equiv_normalizer_eq]
    intro p hp
    refine ⟨c p, hV.2.2 ⟨p, hp, rfl⟩, ?_⟩
    simp
  rw [eq_top_iff]
  calc (⊤ : Subgroup (alternatingGroup (Fin 7)))
      = (vOne.comap ι ⊔ vTwo.comap ι).map c.symm.toMonoidHom := by
        rw [htop, Subgroup.map_top_of_surjective _ c.symm.surjective]
    _ = (vOne.comap ι).map c.symm.toMonoidHom ⊔ (vTwo.comap ι).map c.symm.toMonoidHom :=
        Subgroup.map_sup _ _ _
    _ ≤ _ := sup_le (le_sSup (hmem _ h1.2.1)) (le_sSup (hmem _ h2.2.1))

end A7

theorem gen_of_nine_of_mulEquiv {H : Type*} [Group H] (φ : H ≃* alternatingGroup (Fin 7))
    {P : Subgroup H} (hP9 : Nat.card P = 9) :
    sSup {Y : Subgroup H | ¬ 3 ∣ Nat.card Y ∧ P ≤ Subgroup.normalizer (Y : Set H)} = ⊤ := by
  have h := A7.gen_of_nine (P := P.map φ.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective φ.injective, hP9])
  rw [eq_top_iff]
  intro y _
  have hy : φ y ∈ sSup {Y : Subgroup (alternatingGroup (Fin 7)) | ¬ 3 ∣ Nat.card Y ∧
      P.map φ.toMonoidHom ≤ Subgroup.normalizer (Y : Set (alternatingGroup (Fin 7)))} := by
    rw [h]; exact Subgroup.mem_top _
  have hle : sSup {Y : Subgroup (alternatingGroup (Fin 7)) | ¬ 3 ∣ Nat.card Y ∧
      P.map φ.toMonoidHom ≤ Subgroup.normalizer (Y : Set (alternatingGroup (Fin 7)))} ≤
      (sSup {Y : Subgroup H | ¬ 3 ∣ Nat.card Y ∧ P ≤ Subgroup.normalizer (Y : Set H)}).map
        φ.toMonoidHom := by
    refine sSup_le fun Y hY => ?_
    have hYmem : Y.map φ.symm.toMonoidHom ∈ {Y : Subgroup H | ¬ 3 ∣ Nat.card Y ∧
        P ≤ Subgroup.normalizer (Y : Set H)} := by
      refine ⟨by rw [Subgroup.card_map_of_injective φ.symm.injective]; exact hY.1, ?_⟩
      rw [← Subgroup.map_equiv_normalizer_eq]
      intro p hp
      refine ⟨φ p, hY.2 ⟨p, hp, rfl⟩, ?_⟩
      simp
    have := Subgroup.map_mono (f := φ.toMonoidHom) (le_sSup hYmem)
    rwa [Subgroup.map_map, show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id _ by
      ext; simp, Subgroup.map_id] at this
  obtain ⟨z, hz, hzy⟩ := hle hy
  rwa [← φ.injective hzy]

theorem sigGenConcl_of_alt7 {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    {P : Subgroup (MulAut X)} (hP : IsPGroup 3 P) {F : Subgroup X} (hF3 : IsPGroup 3 F)
    (hF : ∀ x : X, (∀ σ ∈ P, σ x = x) → x ∈ F) {K₀ : Subgroup X}
    (φ : K₀ ≃* alternatingGroup (Fin 7)) {E : Subgroup X} (hEK : E ≤ K₀) (hE9 : Nat.card E = 9)
    (hPE : ∀ σ ∈ P, ∃ e ∈ E, ∀ k ∈ K₀, σ k = e * k * e⁻¹) :
    SigGenConcl P (K₀.map (MulAut.conj : X →* MulAut X)) := by
  refine sigGenConcl_of_gen hZ hP hF3 hF ?_
  set E' := E.subgroupOf K₀ with hE'
  have hE'9 : Nat.card E' = 9 := by
    rw [hE', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hE9]
  have hgen := gen_of_nine_of_mulEquiv φ hE'9
  intro k hk
  have hk' : (⟨k, hk⟩ : K₀) ∈ sSup {Y : Subgroup K₀ | ¬ 3 ∣ Nat.card Y ∧
      E' ≤ Subgroup.normalizer (Y : Set K₀)} := by
    rw [hgen]; exact Subgroup.mem_top _
  have hle : (sSup {Y : Subgroup K₀ | ¬ 3 ∣ Nat.card Y ∧
      E' ≤ Subgroup.normalizer (Y : Set K₀)}).map K₀.subtype ≤
      sSup {Y : Subgroup X | Y ≤ K₀ ∧ ¬ 3 ∣ Nat.card Y ∧ ∀ σ ∈ P, ∀ y ∈ Y, σ y ∈ Y} := by
    rw [(Subgroup.gc_map_comap _).l_sSup]
    refine iSup₂_le fun Y hY => le_sSup ⟨Subgroup.map_subtype_le Y, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective K₀.subtype_injective]; exact hY.1
    · rintro σ hσ _ ⟨y, hy, rfl⟩
      obtain ⟨e, heE, he⟩ := hPE σ hσ
      have heN := hY.2 (Subgroup.mem_subgroupOf.mpr (show ((⟨e, hEK heE⟩ : K₀) : X) ∈ E from heE))
      refine ⟨⟨e, hEK heE⟩ * y * ⟨e, hEK heE⟩⁻¹, (Subgroup.mem_normalizer_iff.mp heN y).mp hy, ?_⟩
      simp [he y y.2]
  exact hle ⟨⟨k, hk⟩, hk', rfl⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
