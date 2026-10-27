module

public import CFSG.RankThree.GF2n.Stroth80.Sec34Inputs
public import CFSG.RankThree.GF2n.Stroth80.Sec37Inputs
public import CFSG.LocalAnalysis.SteinbergCCSplitActionRootGroups
public import CFSG.LocalAnalysis.SteinbergCCTwoRootGroupsGenerate
public import CFSG.Timmesfeld.ARS.BasicRankOne
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4SL2

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.LocalAnalysis CFSG.Timmesfeld CFSG.Timmesfeld.ARS

theorem hksNormal_holds : HKSNormalStatement := by
  intro H _ _ Ω _ _ _ m hm hΩ h2 α R hRα hRn hRel hreg
  classical
  haveI : MulAction.IsPretransitive H Ω :=
    MulAction.isPretransitive_of_is_two_pretransitive (h2 := h2)
  have htr : ∀ x y : Ω, ∃ g : H, g • x = y := MulAction.exists_smul_eq H
  have hq4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h3 : 3 ≤ Nat.card Ω := by rw [hΩ]; omega
  obtain ⟨-, ⟨V, ⟨hD, hVα⟩, -⟩, -, -⟩ :=
    split_action_conjugate_root_group_construction htr h3 α R hRα hRn hreg
  obtain ⟨β, hβα⟩ : ∃ β : Ω, β ≠ α := by
    haveI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_ne α
  have hαβ : α ≠ β := hβα.symm
  obtain ⟨γ, hγα, hγβ⟩ : ∃ γ : Ω, γ ≠ α ∧ γ ≠ β := by
    by_contra hcon
    push Not at hcon
    have hsub : (Set.univ : Set Ω) ⊆ {α, β} := fun x _ => by
      by_cases hxa : x = α
      · exact Or.inl hxa
      · exact Or.inr (hcon x hxa)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ] at h1
    have h4 := Set.ncard_pair hαβ
    omega
  have hVfix := hD.fixes
  have hVreg := hD.regular
  have hfree : ∀ (x : Ω) (u : H), u ∈ V x → ∀ y, y ≠ x → u • y = y → u = 1 := by
    intro x u hu y hy huy
    obtain ⟨w, -, hw⟩ := hVreg x y y hy hy
    have h1 : (⟨u, hu⟩ : V x) = w := hw _ huy
    have h4 : (1 : V x) = w := hw 1 (one_smul H y)
    exact congrArg Subtype.val (h1.trans h4.symm)
  have hopp : Opposite (V α) (V β) := by
    refine ⟨?_, ?_, ?_⟩
    · intro hVV
      obtain ⟨u, hu, -⟩ := hVreg α β γ hβα hγα
      have hmem : (u : H) ∈ V β := hVV ▸ u.2
      exact hγβ (hu.symm.trans (hVfix β u hmem))
    · intro a ha ha1
      have haβ : a • β ≠ β := fun h => ha1 (hfree α a ha β hβα h)
      have haα : a • β ≠ α := by
        intro h
        apply hβα
        have h5 : a • α = α := hVfix α a ha
        calc β = a⁻¹ • a • β := (inv_smul_smul a β).symm
          _ = a⁻¹ • α := by rw [h]
          _ = α := by rw [inv_smul_eq_iff, h5]
      obtain ⟨b, hbα, -⟩ := hVreg β α (a • β) hαβ haβ
      refine ⟨b, b.2, fun hb1 => ?_, ?_⟩
      · have h6 : (b : H) • α = α := by rw [hb1, one_smul]
        exact haα (hbα.symm.trans h6)
      · show (V α).map (MulAut.conj (b : H)).toMonoidHom = (V β).map (MulAut.conj a).toMonoidHom
        rw [hD.conj b α, hD.conj a β, hbα]
    · intro b hb hb1
      have hbα : b • α ≠ α := fun h => hb1 (hfree β b hb α hαβ h)
      have hbβ : b • α ≠ β := by
        intro h
        apply hαβ
        have h5 : b • β = β := hVfix β b hb
        calc α = b⁻¹ • b • α := (inv_smul_smul b α).symm
          _ = b⁻¹ • β := by rw [h]
          _ = β := by rw [inv_smul_eq_iff, h5]
      obtain ⟨a, haβ, -⟩ := hVreg α β (b • α) hβα hbα
      refine ⟨a, a.2, fun ha1 => ?_, ?_⟩
      · have h6 : (a : H) • β = β := by rw [ha1, one_smul]
        exact hbβ (haβ.symm.trans h6)
      · show (V β).map (MulAut.conj (a : H)).toMonoidHom = (V α).map (MulAut.conj b).toMonoidHom
        rw [hD.conj a β, hD.conj b α, haβ]
  have hsq : ∀ a ∈ V α, a * a = 1 := by
    intro a ha
    rw [hVα] at ha
    have h7 := hRel.2 a ha
    rwa [pow_two] at h7
  have hr := hopp.isElemAbRankOne_of_mul_self hsq
  have hcardR : Nat.card R = 2 ^ m := by
    have hne : ∀ u : R, (u : H) • β ≠ α := by
      intro u h
      apply hβα
      have h5 : (u : H) • α = α := MulAction.mem_stabilizer_iff.mp (hRα u.2)
      calc β = (u : H)⁻¹ • (u : H) • β := (inv_smul_smul (u : H) β).symm
        _ = (u : H)⁻¹ • α := by rw [h]
        _ = α := by rw [inv_smul_eq_iff, h5]
    have hbij : Function.Bijective
        (fun u : R => (⟨(u : H) • β, hne u⟩ : {x : Ω // x ≠ α})) := by
      constructor
      · intro u u' h
        have h8 : (u : H) • β = (u' : H) • β := congrArg Subtype.val h
        obtain ⟨w, -, hw⟩ := hreg β ((u : H) • β) hβα (hne u)
        exact (hw u rfl).trans (hw u' h8.symm).symm
      · rintro ⟨γ', hγ'⟩
        obtain ⟨u, hu, -⟩ := hreg β γ' hβα hγ'
        exact ⟨u, Subtype.ext hu⟩
    have hsub : Nat.card {x : Ω // x ≠ α} = Nat.card Ω - 1 := by
      letI : Fintype Ω := Fintype.ofFinite Ω
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
        Fintype.card_subtype_eq]
    rw [Nat.card_congr (Equiv.ofBijective _ hbij), hsub, hΩ]
    rfl
  have hcardA : Nat.card ((V α).subgroupOf (V α ⊔ V β)) = 2 ^ m := by
    rw [← hcardR, ← hVα]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  obtain ⟨n, hn2, hn, φ, -, -⟩ :=
    ElemAbRankOne.exists_mulEquiv_SL2 hr (by rw [hcardA]; exact hq4)
  have hnm : n = m := Nat.pow_right_injective le_rfl (hn.symm.trans hcardA)
  subst hnm
  obtain ⟨-, hLn, htrans2, -, -⟩ := two_root_groups_generate_normal_subgroup hD hαβ
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    CFSG.ComponentClassification.Asc75T4.isSimpleGroup_sl2 hn2
  refine ⟨V α ⊔ V β, hLn, φ.isSimpleGroup, ⟨φ⟩, ?_, hVα ▸ le_sup_left⟩
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨l, hl, hla, hlb⟩ := htrans2 a b c d hab hcd
  exact ⟨⟨l, hl⟩, hla, hlb⟩

theorem hksStatement_holds : HKSStatement := by
  intro H _ _ Ω _ _ _ m hm hcard h2 α R hR hRn hRe hreg
  obtain ⟨L, hLn, hLs, hLiso, hL2, -⟩ := hksNormal_holds H Ω m hm hcard h2 α R hR hRn hRe hreg
  exact ⟨L, hLn, hLs, hLiso, hL2⟩

end CFSG.RankThree.GF2n.Stroth80
