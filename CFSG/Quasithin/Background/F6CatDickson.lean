module

public import CFSG.Quasithin.Background.F6CatAssembly
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification

public section

namespace CFSG.Quasithin

namespace F6

theorem card_dvd_of_isPGroup_psl2 {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ f) {H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)}
    (hH : IsPGroup p ↥H) : Nat.card ↥H ∣ p ^ f := by
  obtain ⟨P, hP⟩ := hH.exists_le_sylow
  obtain ⟨e⟩ := CFSG.BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF P
  have hPcard : Nat.card ↥(P : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) =
      p ^ f := by
    rw [← Nat.card_congr e.toEquiv]
    exact hF
  exact hPcard ▸ Subgroup.card_dvd_of_le hP

theorem dicksonPSL2_holds : DicksonPSL2 := by
  intro p f _ hf H
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hg : Nat.gcd (p ^ f - 1) 2 = Nat.gcd 2 (p ^ f - 1) := Nat.gcd_comm _ _
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF H with
      hel | ⟨z, hz, hHz, hc⟩ | ⟨z, hz, -, hd⟩ | h4 | h5 | h6 |
      ⟨m, t, ht, htq, N, C, hN, hNel, hNc, hCc, hCt, hdisj, hNC⟩ | ⟨m, -, hm, he⟩ |
      ⟨m, -, hm, he⟩
  · refine Or.inl ⟨(CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p H).mp hel, ?_⟩
    have hpg : IsPGroup p ↥H := CFSG.IsElementaryAbelian.isPGroup p ↥H
    obtain ⟨k, hk⟩ := hpg.exists_card_eq
    have hdvd := card_dvd_of_isPGroup_psl2 hF hpg
    rw [hk] at hdvd
    exact ⟨k, (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hdvd, hk⟩
  · rw [hF, hg] at hz
    subst hHz
    exact Or.inr (Or.inl ⟨hc, hz.symm⟩)
  · rw [hF, hg] at hz
    exact Or.inr (Or.inr (Or.inl ⟨z, hz.symm, hd⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
  · have hCN : C.IsComplement' N := by
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj.symm ?_
      rw [← Subgroup.mul_normal C N, sup_comm, hNC, Subgroup.coe_top]
    let φ : ↥H ⧸ N ≃* ↥C := hCN.QuotientMulEquiv
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, t, N, hN,
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p N).mp hNel, hNc,
      isCyclic_of_surjective φ.symm φ.symm.surjective, ?_, ht, hg ▸ htq⟩))))))
    rw [Nat.card_congr φ.toEquiv, hCt]
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, he⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, hm, he⟩)))))))

theorem l2DicksonFacts_holds : L2DicksonFacts :=
  l2DicksonFacts_of_dickson dicksonPSL2_holds

structure F618QSInputs' : Prop where
  theoremC : NativeTheoremCSection
  goldschmidt : GoldschmidtS3ListCat.{0}
  recogE4 : F618RecogE4
  recogD8 : F618RecogD8
  recogZ2D8 : F618RecogZ2D8
  recogZ4wrZ2 : F618RecogZ4wrZ2
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

theorem F618QSInputs'.toF618QSInputs
    (I : F618QSInputs') : F618QSInputs :=
  ⟨I.theoremC, I.goldschmidt, dicksonPSL2_holds, I.recogE4, I.recogD8, I.recogZ2D8,
    I.recogZ4wrZ2, I.recogG22M12, I.recogAutM12, I.sylowG22Prime, I.shapeG22, I.shapeM12,
    I.shapeAutM12, I.inspectPGL2, I.inspectA7, I.inspectS7, I.inspectPSigmaL2⟩

theorem f618QuasisimpleCaseCat_of'
    (I : F618QSInputs') : F618QuasisimpleCaseCat :=
  f618QuasisimpleCaseCat_of I.toF618QSInputs

theorem theoremF618Cat_of'
    (hNQ : F617NonquasisimpleCaseCat) (I : F618QSInputs') :
    TheoremF618Cat :=
  theoremF618Cat_of hNQ I.toF618QSInputs

end F6

end CFSG.Quasithin
