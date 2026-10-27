module

public import CFSG.Quasithin.Background.F6CatRecogL2
public import CFSG.Quasithin.Background.F6CatDickson

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace F6

@[expose] def F618RecogZ2D8SQT : Prop :=
  ∀ (D : Type) [Group D] [Finite D], F618RecogSettingSQT D →
    (∃ S : Sylow 2 D, Nonempty (↥S ≃* Multiplicative (ZMod 2) × DihedralGroup 4)) →
    (∃ p : ℕ, p.Prime ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsL2FieldExtCat p D) ∨ IsHatSym 6 D ∨
      Nonempty (D ≃* Equiv.Perm (Fin 7)) ∨ IsHatSym 7 D

theorem f618RecogZ2D8SQT_of (h : F618RecogZ2D8) : F618RecogZ2D8SQT :=
  fun D _ _ hS => h D hS.toF618RecogSetting

@[expose] def F618RecogZ4wrZ2SQT : Prop :=
  ∀ (D : Type) [Group D] [Finite D], F618RecogSettingSQT D →
    (∃ S : Sylow 2 D,
      Nonempty (↥S ≃* Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2))) →
    ∃ p : ℕ, (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSLEps3 p D

theorem f618RecogZ4wrZ2SQT_of (h : F618RecogZ4wrZ2) : F618RecogZ4wrZ2SQT :=
  fun D _ _ hS => h D hS.toF618RecogSetting

structure F618QSInputsMS : Prop where
  theoremC : NativeTheoremCSection
  sqtSection : NativeSQTSection
  goldschmidt : GoldschmidtS3ListCat.{0}
  recogZ2D8 : F618RecogZ2D8SQT
  recogZ4wrZ2 : F618RecogZ4wrZ2SQT
  recogG22M12 : F618RecogG22M12
  recogAutM12 : F618RecogAutM12
  sylowG22Prime : G22PrimeSylowFact
  shapeG22 : G22AmalgamShapeFact
  shapeM12 : M12AmalgamShapeFact
  shapeAutM12 : AutM12AmalgamShapeFact
  inspectPGL2 : PGL2InspectionFact
  inspectA7 : A7InspectionFact
  inspectS7 : S7InspectionFact
  inspectPSigmaL2 : PSigmaL2InspectionFact

namespace MS

variable {D : Type} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

section Cases

variable (I : F618QSInputsMS)
include I

omit I in
theorem caseII
    (h : IsGoldschmidtTriple G₁ G₂) (hS : F618RecogSettingSQT D)
    (ho : IsGoldCaseII G₁ G₂) : IsF618CaseFour G₁ G₂ := by
  obtain ⟨⟨e₁⟩, ⟨eT⟩, ⟨e₂⟩⟩ := ho
  obtain ⟨p, hp, hp8, hL⟩ := f618RecogE4_of_sqt D hS (exists_sylow_of_inf h eT)
  refine ⟨⟨p, hp, ?_, hL⟩, ⟨eT⟩, ⟨e₁⟩, ⟨e₂⟩⟩
  obtain ⟨-, K, _, _, hK, ⟨ε⟩⟩ := hL
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hD := l2DicksonFacts_holds p 1 K hp hp2 le_rfl hK
    (G₁.map ε.toMonoidHom)
  have h12 := hD.1 ⟨(G₁.equivMapOfInjective ε.toMonoidHom ε.injective).symm.trans e₁⟩
  rw [pow_one] at h12
  omega

theorem caseD8
    (h : IsGoldschmidtTriple G₁ G₂) (hS : F618RecogSettingSQT D)
    (eT : ↥(G₁ ⊓ G₂) ≃* DihedralGroup 4)
    (hty : IsGoldCaseIII G₁ G₂ ∨ IsGoldCaseIV G₁ G₂ ∨
      (Nonempty (↥G₁ ≃* Equiv.Perm (Fin 4)) ∧ Nonempty (↥G₂ ≃* Equiv.Perm (Fin 4)))) :
    IsF618CaseFive G₁ G₂ ∨ IsF618CaseSix G₁ G₂ ∨ IsF618CaseSeven G₁ G₂ := by
  have hns := not_isSolvable_of_setting hS.toF618RecogSetting
  rcases f618RecogD8_of_sqt D hS (exists_sylow_of_inf h eT) with
    ⟨p, e, hp, he1, he2, hpe, hL⟩ | hHat6 | ⟨q, hq, hq8, hPGL⟩ | he7 | hHat7
  ·
    have hp2 := ne_two_of_pow_mod_sixteen he1 he2 hpe
    obtain ⟨-, K, _, _, hK, ⟨ε⟩⟩ := id hL
    have hD := l2DicksonFacts_holds p e K hp hp2 he1 hK
    rcases hty with ⟨⟨e₁⟩, -, ⟨e₂⟩⟩ | ⟨-, -, hIV⟩ | ⟨⟨e₁⟩, ⟨e₂⟩⟩
    · have h24 := (hD (G₁.map ε.toMonoidHom)).2.1
        ⟨(G₁.equivMapOfInjective ε.toMonoidHom ε.injective).symm.trans e₁⟩
      exact Or.inr (Or.inl ⟨Or.inr ⟨p, e, hp, he1, he2, hpe, hL⟩, ⟨eT⟩,
        Or.inr ⟨⟨p, e, hp, he1, he2, hpe, h24, hL⟩, ⟨e₁⟩, ⟨e₂⟩⟩⟩)
    · exfalso
      obtain ⟨φ, -, ⟨eN⟩⟩ := hIV
      exact (hD ((φ.ker.map G₂.subtype).map ε.toMonoidHom)).2.2
        ⟨(((φ.ker.map G₂.subtype).equivMapOfInjective ε.toMonoidHom ε.injective).symm.trans
          ((φ.ker.equivMapOfInjective G₂.subtype G₂.subtype_injective).symm.trans eN))⟩
    · exact Or.inr (Or.inl ⟨Or.inr ⟨p, e, hp, he1, he2, hpe, hL⟩, ⟨eT⟩, Or.inl ⟨⟨e₁⟩, ⟨e₂⟩⟩⟩)
  ·
    obtain ⟨ψ, -, hker⟩ := exists_hom_of_isHatAlt hHat6
    obtain ⟨hi₁, hi₂⟩ := injOn_of_card_ker_eq_three h hns ψ hker
    rcases hty with ⟨⟨e₁⟩, -, -⟩ | ⟨-, -, hIV⟩ | ⟨⟨e₁⟩, ⟨e₂⟩⟩
    · exfalso
      obtain ⟨y, hy, hyf⟩ := exists_mem_pow_facts e₁ dihedral_twelve_order_six
      exact not_pow_facts_alternating_six (ψ y) (pow_facts_map ψ hi₁ hy hyf)
    · exfalso
      obtain ⟨y, hy, hyf⟩ := exists_mem_order_six_of_isExtensionOf hIV
      exact not_pow_facts_alternating_six (ψ y) (pow_facts_map ψ hi₂ hy hyf)
    · exact Or.inr (Or.inl ⟨Or.inl hHat6, ⟨eT⟩, Or.inl ⟨⟨e₁⟩, ⟨e₂⟩⟩⟩)
  ·
    obtain ⟨K, _, _, hK, ⟨ε⟩⟩ := id hPGL
    obtain ⟨h', ⟨ι₁⟩, ⟨ι₂⟩, ⟨ιT⟩⟩ := image_triple_mulEquiv h ε
    obtain ⟨hIII, hnIV, hnS4⟩ := I.inspectPGL2 K (hK ▸ hq) (hK ▸ hq8) _ _ h'
    rcases hty with ⟨⟨e₁⟩, -, ⟨e₂⟩⟩ | ⟨⟨e₁⟩, -, hIV⟩ | ⟨⟨e₁⟩, ⟨e₂⟩⟩
    · have hc := hIII ⟨⟨ι₁.trans e₁⟩, ⟨ιT.trans eT⟩, ⟨ι₂.trans e₂⟩⟩
      rw [hK] at hc
      exact Or.inl ⟨⟨q, hq, hc, hPGL⟩, ⟨eT⟩, ⟨e₁⟩, ⟨e₂⟩⟩
    · exact absurd ⟨⟨ι₁.trans e₁⟩, ⟨ιT.trans eT⟩, isExtensionOf_of_mulEquiv ι₂ hIV⟩ hnIV
    · exact absurd ⟨⟨ι₁.trans e₁⟩, ⟨ι₂.trans e₂⟩⟩ hnS4
  ·
    obtain ⟨e7⟩ := he7
    rcases hty with ⟨⟨e₁⟩, -, -⟩ | ⟨⟨e₁⟩, -, hIV⟩ | ⟨⟨e₁⟩, ⟨e₂⟩⟩
    · exfalso
      obtain ⟨y, hy, hyf⟩ := exists_mem_pow_facts e₁ dihedral_twelve_order_twelve
      exact not_pow_facts_alternating_seven (e7 y) (pow_facts_map e7.toMonoidHom
        (fun _ _ hx => e7.injective (hx.trans (map_one e7).symm)) hy hyf)
    · exact Or.inr (Or.inr ⟨Or.inl ⟨e7⟩, ⟨eT⟩, ⟨e₁⟩, hIV⟩)
    · exfalso
      obtain ⟨h', ⟨ι₁⟩, ⟨ι₂⟩, -⟩ := image_triple_mulEquiv h e7
      exact I.inspectA7 _ _ h' ⟨⟨ι₁.trans e₁⟩, ⟨ι₂.trans e₂⟩⟩
  ·
    obtain ⟨ψ, hψ, hker⟩ := exists_hom_of_isHatAlt hHat7
    obtain ⟨hi₁, hi₂⟩ := injOn_of_card_ker_eq_three h hns ψ hker
    rcases hty with ⟨⟨e₁⟩, -, -⟩ | ⟨⟨e₁⟩, -, hIV⟩ | ⟨⟨e₁⟩, ⟨e₂⟩⟩
    · exfalso
      obtain ⟨y, hy, hyf⟩ := exists_mem_pow_facts e₁ dihedral_twelve_order_twelve
      exact not_pow_facts_alternating_seven (ψ y) (pow_facts_map ψ hi₁ hy hyf)
    · exact Or.inr (Or.inr ⟨Or.inr hHat7, ⟨eT⟩, ⟨e₁⟩, hIV⟩)
    · exfalso
      obtain ⟨H₁, H₂, h', ⟨ι₁⟩, ⟨ι₂⟩⟩ := exists_image_triple h hns ψ hψ hker
      exact I.inspectA7 _ _ h' ⟨⟨ι₁.trans e₁⟩, ⟨ι₂.trans e₂⟩⟩

theorem caseZ2D8 (h : IsGoldschmidtTriple G₁ G₂) (hS : F618RecogSettingSQT D)
    (eT : ↥(G₁ ⊓ G₂) ≃* Multiplicative (ZMod 2) × DihedralGroup 4)
    (e₁ : ↥G₁ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))
    (hty : Nonempty (↥G₂ ≃* Equiv.Perm (Fin 3) × DihedralGroup 4) ∨
      Nonempty (↥G₂ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) :
    IsF618CaseEightCat G₁ G₂ ∨ IsF618CaseNineCat G₁ G₂ := by
  have hns := not_isSolvable_of_setting hS.toF618RecogSetting
  rcases I.recogZ2D8 D hS (exists_sylow_of_inf h eT) with ⟨p, hp, hp8, hF⟩ | hHat6 | he7 | hHat7
  ·
    rcases hty with he₂ | he₂ <;> obtain ⟨e₂⟩ := he₂
    · obtain ⟨-, K, _, _, hK, ⟨ε⟩⟩ := id hF
      obtain ⟨h', -, ⟨ι₂⟩, -⟩ := image_triple_mulEquiv h ε
      have hc := I.inspectPSigmaL2 p K hp hK hp8 _ _ h' ⟨ι₂.trans e₂⟩
      exact Or.inr ⟨Or.inr (Or.inr ⟨p, hp, hc, hF⟩), ⟨eT⟩, ⟨e₁⟩, ⟨e₂⟩⟩
    · exact Or.inl ⟨Or.inr ⟨p, hp, hp8, hF⟩, ⟨eT⟩, ⟨e₁⟩, ⟨e₂⟩⟩
  ·
    rcases hty with he₂ | he₂ <;> obtain ⟨e₂⟩ := he₂
    · exfalso
      obtain ⟨φ, -, hker, -⟩ := hHat6
      obtain ⟨-, hi₂⟩ := injOn_of_card_ker_eq_three h hns φ hker
      obtain ⟨y, hy, hyf⟩ := exists_mem_pow_facts e₂ s3_d8_order_twelve
      exact not_pow_facts_perm_six (φ y) (pow_facts_map φ hi₂ hy hyf)
    · exact Or.inl ⟨Or.inl hHat6, ⟨eT⟩, ⟨e₁⟩, ⟨e₂⟩⟩
  ·
    obtain ⟨e7⟩ := he7
    rcases hty with he₂ | he₂ <;> obtain ⟨e₂⟩ := he₂
    · exact Or.inr ⟨Or.inl ⟨e7⟩, ⟨eT⟩, ⟨e₁⟩, ⟨e₂⟩⟩
    · exfalso
      obtain ⟨h', ⟨ι₁⟩, ⟨ι₂⟩, -⟩ := image_triple_mulEquiv h e7
      exact I.inspectS7 _ _ h' ⟨⟨ι₁.trans e₁⟩, ⟨ι₂.trans e₂⟩⟩
  ·
    rcases hty with he₂ | he₂ <;> obtain ⟨e₂⟩ := he₂
    · exact Or.inr ⟨Or.inr (Or.inl hHat7), ⟨eT⟩, ⟨e₁⟩, ⟨e₂⟩⟩
    · exfalso
      obtain ⟨φ, hφ, hker, -⟩ := hHat7
      obtain ⟨H₁, H₂, h', ⟨ι₁⟩, ⟨ι₂⟩⟩ := exists_image_triple h hns φ hφ hker
      exact I.inspectS7 _ _ h' ⟨⟨ι₁.trans e₁⟩, ⟨ι₂.trans e₂⟩⟩

theorem caseG22Prime (h : IsGoldschmidtTriple G₁ G₂) (hS : F618RecogSettingSQT D)
    (ho : IsGoldCaseG22Prime G₁ G₂) : IsF618CaseTen G₁ G₂ := by
  obtain ⟨⟨W, _, _, K₁, K₂, hW, ⟨-, -, -, S, hSK⟩, φ₁, φ₂, hag₁, hag₂⟩, -, hq₁, hq₂, hR₁, ⟨eR₂⟩⟩ :=
    ho
  have eT : ↥(G₁ ⊓ G₂) ≃* Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2) :=
    ((infMulEquivOfAmalgamIso φ₁ φ₂ hag₁ hag₂).trans (MulEquiv.subgroupCongr hSK.symm)).trans
      (I.sylowG22Prime W hW S).some
  obtain ⟨p, hp8, hSL⟩ := I.recogZ4wrZ2 D hS (exists_sylow_of_inf h eT)
  exact ⟨⟨p, hp8, hSL⟩, ⟨eT⟩,
    isExtensionWith_of_quotientPCore hq₁.some (isCentralProduct₂_of_mulEquiv (pCoreOfEquiv G₁) hR₁),
    isExtensionOf_of_quotientPCore hq₂.some eR₂⟩

theorem caseG22M12 (h : IsGoldschmidtTriple G₁ G₂) (hS : F618RecogSettingSQT D)
    (ho : IsGoldCaseG22 G₁ G₂ ∨ IsGoldCaseM12 G₁ G₂) :
    IsF618CaseEleven G₁ G₂ ∨ IsF618CaseTwelve G₁ G₂ := by
  have hrec := I.recogG22M12 D G₁ G₂ hS.toF618RecogSetting h ho
  obtain ⟨hTsh, hG₁sh, hG₂sh⟩ :
      IsExtensionOf ↥(G₁ ⊓ G₂) (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
          (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
        IsExtensionWith ↥G₁ (Equiv.Perm (Fin 3))
          (fun N => IsCentralProduct₂ ↥N (QuaternionGroup 2) (QuaternionGroup 2)) ∧
        IsExtensionOf ↥G₂ (DihedralGroup 6)
          (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
    rcases ho with ⟨⟨W, _, _, K₁, K₂, hW, hTL, φ₁, φ₂, hag₁, hag₂⟩, -, hq₁, hq₂, hsp, hc₂⟩ |
        ⟨⟨W, _, _, K₁, K₂, hW, hTL, φ₁, φ₂, hag₁, hag₂⟩, -, hq₁, hq₂, hcp, hc₂⟩
    · obtain ⟨aT, aR, a₂⟩ := I.shapeG22 W K₁ K₂ hW hTL (quotientPCoreIsL22_of_mulEquiv φ₁ hq₁)
        (quotientPCoreIsL22_of_mulEquiv φ₂ hq₂)
        (isSpecialTwoOnePlusFour_of_mulEquiv (pCoreOfCongr φ₁).symm hsp)
        (by rw [← Nat.card_congr (pCoreOfCongr φ₂).toEquiv]; exact hc₂)
      exact ⟨isExtensionOf_of_mulEquiv (infMulEquivOfAmalgamIso φ₁ φ₂ hag₁ hag₂) aT,
        isExtensionWith_of_quotientPCore hq₁.some
          (isCentralProduct₂_of_mulEquiv ((pCoreOfEquiv G₁).trans (pCoreOfCongr φ₁)) aR),
        isExtensionOf_of_mulEquiv φ₂ a₂⟩
    · obtain ⟨aT, a₂⟩ := I.shapeM12 W K₁ K₂ hW hTL (quotientPCoreIsL22_of_mulEquiv φ₁ hq₁)
        (quotientPCoreIsL22_of_mulEquiv φ₂ hq₂)
        (isCentralProduct₂_of_mulEquiv (pCoreOfCongr φ₁).symm hcp)
        (by rw [← Nat.card_congr (pCoreOfCongr φ₂).toEquiv]; exact hc₂)
      exact ⟨isExtensionOf_of_mulEquiv (infMulEquivOfAmalgamIso φ₁ φ₂ hag₁ hag₂) aT,
        isExtensionWith_of_quotientPCore hq₁.some
          (isCentralProduct₂_of_mulEquiv (pCoreOfEquiv G₁) hcp),
        isExtensionOf_of_mulEquiv φ₂ a₂⟩
  rcases hrec with ⟨p, hp8, hgr⟩ | hM
  · exact Or.inl ⟨⟨p, hp8, hgr⟩, hTsh, hG₁sh, hG₂sh⟩
  · exact Or.inr ⟨hM, hTsh, hG₁sh, hG₂sh⟩

theorem caseAutM12 (h : IsGoldschmidtTriple G₁ G₂) (hS : F618RecogSettingSQT D)
    (ho : IsGoldCaseAutM12Cat G₁ G₂) : IsF618CaseThirteen G₁ G₂ := by
  have hD := I.recogAutM12 D G₁ G₂ hS.toF618RecogSetting h ho
  obtain ⟨⟨W, _, _, K₁, K₂, hW, hTL, φ₁, φ₂, hag₁, hag₂⟩, -, hq₁, hq₂, hext, hc₁, hz₁, hc₂⟩ := ho
  obtain ⟨aT, a₂⟩ := I.shapeAutM12 W K₁ K₂ hW hTL (quotientPCoreIsL22_of_mulEquiv φ₁ hq₁)
    (quotientPCoreIsL22_of_mulEquiv φ₂ hq₂)
    (isExtensionWith_centralProduct_of_mulEquiv φ₁.symm hext)
    (by rw [← Nat.card_congr (pCoreOfCongr φ₁).toEquiv]; exact hc₁)
    (by rw [← card_centerOf_eq (pCoreOfCongr φ₁)]; exact hz₁)
    (by rw [← Nat.card_congr (pCoreOfCongr φ₂).toEquiv]; exact hc₂)
  exact ⟨hD, isExtensionOf_of_mulEquiv (infMulEquivOfAmalgamIso φ₁ φ₂ hag₁ hag₂) aT, hext,
    isExtensionOf₃_of_mulEquiv φ₂ a₂⟩

theorem isF618CaseOrientedCat_of_oriented
    (h : IsGoldschmidtTriple G₁ G₂)
    (hS : F618RecogSettingSQT D) (ho : IsGoldCaseOrientedCat G₁ G₂) :
    IsF618CaseOrientedCat G₁ G₂ := by
  unfold IsF618CaseOrientedCat
  rcases ho with hI | hII | hIII | hIV | hV | hVI
  · exact absurd (false_of_isGoldCaseI h hS.quasisimple hI) not_false
  · exact Or.inr (Or.inr (Or.inr (Or.inl (caseII h hS hII))))
  · rcases caseD8 I h hS hIII.2.1.some (Or.inl hIII) with h5 | h6 | h7
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))))
  · rcases caseD8 I h hS hIV.2.1.some (Or.inr (Or.inl hIV)) with h5 | h6 | h7
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))))
  · rcases caseZ2D8 I h hS hV.2.1.some hV.1.some (Or.inl hV.2.2) with h8 | h9
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9))))))))
  · rcases hVI with hL32 | hSp | hG22 | hG22' | hM12 | hAut
    · obtain ⟨-, -, ⟨e₁⟩, ⟨e₂⟩⟩ := hL32
      rcases caseD8 I h hS (nonempty_inf_mulEquiv_dihedral_of_left h e₁).some
          (Or.inr (Or.inr ⟨⟨e₁⟩, ⟨e₂⟩⟩)) with h5 | h6 | h7
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))))
    · obtain ⟨-, -, ⟨e₁⟩, he₂⟩ := hSp
      rcases caseZ2D8 I h hS (nonempty_inf_mulEquiv_z2_dihedral_of_left h e₁).some e₁
          (Or.inr he₂) with h8 | h9
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9))))))))
    · rcases caseG22M12 I h hS (Or.inl hG22) with h11 | h12
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl h11))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl h12)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (caseG22Prime I h hS hG22'))))))))))
    · rcases caseG22M12 I h hS (Or.inr hM12) with h11 | h12
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl h11))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl h12)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (caseAutM12 I h hS hAut))))))))))))

end Cases

end MS

theorem f618QuasisimpleCaseCat_ofMS
    (I : F618QSInputsMS) : F618QuasisimpleCaseCat := by
  intro D _ _ G₁ G₂ h hX hF hL
  have hS := f618RecogSettingSQT_of I.theoremC I.sqtSection hX hF hL
  obtain ⟨X, _, _, -, ⟨e⟩⟩ := hX
  have hA : IsGoldschmidtAmalgam G₁ G₂ := ⟨h, (remark_f6_15 e).2⟩
  rcases I.goldschmidt D G₁ G₂ hA with ho | ho
  · exact Or.inl (MS.isF618CaseOrientedCat_of_oriented I h hS ho)
  · exact Or.inr (MS.isF618CaseOrientedCat_of_oriented I h.symm hS ho)

theorem theoremF618Cat_ofMS
    (hNQ : F617NonquasisimpleCaseCat) (I : F618QSInputsMS) :
    TheoremF618Cat :=
  theoremF618Cat_of_cases hNQ (f618QuasisimpleCaseCat_ofMS I)

end F6

end CFSG.Quasithin
