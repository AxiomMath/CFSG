module

public import CFSG.Quasithin.Background.F6CatInputs
public import CFSG.Quasithin.Background.F6CatSylow
public import CFSG.Quasithin.Background.F6CatSmall
public import CFSG.Quasithin.Background.F6CatIso
public import CFSG.Quasithin.Background.F6CatL2
public import CFSG.Quasithin.Background.F6CatTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace F6

structure F618QSInputs : Prop where
  theoremC : NativeTheoremCSection
  goldschmidt : GoldschmidtS3ListCat.{0}
  dickson : DicksonPSL2
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

variable {D : Type} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

omit [Finite D] in
theorem exists_sylow_of_inf (h : IsGoldschmidtTriple G₁ G₂) {X : Type*} [Group X]
    (e : ↥(G₁ ⊓ G₂) ≃* X) : ∃ S : Sylow 2 D, Nonempty (↥S ≃* X) := by
  obtain ⟨T, hT⟩ := h.sylow
  exact ⟨T, ⟨(MulEquiv.subgroupCongr hT).trans e⟩⟩

theorem not_isSolvable_of_setting (hS : F618RecogSetting D) : ¬ Group.IsSolvable D := by
  intro hsolv
  have : Group.IsSolvable ↥(twoResidual (⊤ : Subgroup D)) := inferInstance
  have : Nontrivial ↥(twoResidual (⊤ : Subgroup D)) :=
    CFSG.LocalCores.isQuasisimple_nontrivial hS.quasisimple
  have : Group.IsPerfect ↥(twoResidual (⊤ : Subgroup D)) := hS.quasisimple.1
  have hsL : Group.IsSolvable ↥(twoResidual (⊤ : Subgroup D)) := inferInstance
  exact Group.IsPerfect.not_isSolvable (G := ↥(twoResidual (⊤ : Subgroup D))) hsL

theorem exists_mem_pow_facts {G X : Type*} [Group G] [Group X] {H : Subgroup G} (e : ↥H ≃* X)
    {x : X} {n a b : ℕ} (hx : x ^ n = 1 ∧ x ^ a ≠ 1 ∧ x ^ b ≠ 1) :
    ∃ y ∈ H, y ^ n = 1 ∧ y ^ a ≠ 1 ∧ y ^ b ≠ 1 :=
  ⟨(e.symm x : G), (e.symm x).2, pow_facts_of_injective (H.subtype.comp e.symm.toMonoidHom)
    (H.subtype_injective.comp e.symm.injective) hx⟩

theorem pow_facts_map {G G' : Type*} [Group G] [Group G'] {H : Subgroup G} (ψ : G →* G')
    (hψ : ∀ x ∈ H, ψ x = 1 → x = 1) {y : G} (hy : y ∈ H) {n a b : ℕ}
    (h : y ^ n = 1 ∧ y ^ a ≠ 1 ∧ y ^ b ≠ 1) :
    ψ y ^ n = 1 ∧ ψ y ^ a ≠ 1 ∧ ψ y ^ b ≠ 1 := by
  refine ⟨by rw [← map_pow, h.1, map_one], fun h' => h.2.1 ?_, fun h' => h.2.2 ?_⟩
  · exact hψ _ (H.pow_mem hy a) (by rw [map_pow, h'])
  · exact hψ _ (H.pow_mem hy b) (by rw [map_pow, h'])

omit [Finite D] in
theorem exists_mem_order_six_of_isExtensionOf {H : Subgroup D}
    (hH : IsExtensionOf ↥H (Multiplicative (ZMod 2))
      (Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))) :
    ∃ y ∈ H, y ^ 6 = 1 ∧ y ^ 2 ≠ 1 ∧ y ^ 3 ≠ 1 := by
  obtain ⟨φ, -, ⟨eN⟩⟩ := hH
  obtain ⟨w, -, hw⟩ := exists_mem_pow_facts eN z3_e4_order_six
  refine ⟨(w : D), w.2, ?_⟩
  exact pow_facts_of_injective H.subtype H.subtype_injective hw

theorem not_pow_facts_alternating_six (y : ↥(alternatingGroup (Fin 6)))
    (h : y ^ 6 = 1 ∧ y ^ 2 ≠ 1 ∧ y ^ 3 ≠ 1) : False := by
  have h6 : (y : Equiv.Perm (Fin 6)) ^ 6 = 1 := by simpa using congrArg Subtype.val h.1
  rcases alternating_six_pow_six y (Equiv.Perm.mem_alternatingGroup.mp y.2) h6 with h2 | h3
  · exact h.2.1 (Subtype.ext (by simpa using h2))
  · exact h.2.2 (Subtype.ext (by simpa using h3))

theorem not_pow_facts_alternating_seven (y : ↥(alternatingGroup (Fin 7)))
    (h : y ^ 12 = 1 ∧ y ^ 4 ≠ 1 ∧ y ^ 6 ≠ 1) : False := by
  have h12 : (y : Equiv.Perm (Fin 7)) ^ 12 = 1 := by simpa using congrArg Subtype.val h.1
  rcases alternating_seven_pow_twelve y (Equiv.Perm.mem_alternatingGroup.mp y.2) h12 with
    h4 | h6
  · exact h.2.1 (Subtype.ext (by simpa using h4))
  · exact h.2.2 (Subtype.ext (by simpa using h6))

theorem not_pow_facts_perm_six (y : Equiv.Perm (Fin 6)) (h : y ^ 12 = 1 ∧ y ^ 4 ≠ 1 ∧ y ^ 6 ≠ 1) :
    False := by
  rcases perm_six_pow_twelve y h.1 with h4 | h6
  · exact h.2.1 h4
  · exact h.2.2 h6

theorem injOn_of_card_ker_eq_three (h : IsGoldschmidtTriple G₁ G₂) (hns : ¬ Group.IsSolvable D)
    {Y : Type*} [Group Y] (ψ : D →* Y) (hker : Nat.card ψ.ker = 3) :
    (∀ x ∈ G₁, ψ x = 1 → x = 1) ∧ (∀ x ∈ G₂, ψ x = 1 → x = 1) := by
  have h₁ := inf_eq_bot_of_card_eq_three h hns hker
  have h₂ := inf_eq_bot_of_card_eq_three h.symm hns hker
  refine ⟨fun x hx h1 => ?_, fun x hx h1 => ?_⟩
  · have : x ∈ ψ.ker ⊓ G₁ := ⟨h1, hx⟩
    rw [h₁, Subgroup.mem_bot] at this
    exact this
  · have : x ∈ ψ.ker ⊓ G₂ := ⟨h1, hx⟩
    rw [h₂, Subgroup.mem_bot] at this
    exact this

omit [Finite D] in
theorem exists_hom_of_isHatAlt {n : ℕ} (hD : IsHatAlt n D) :
    ∃ ψ : D →* ↥(alternatingGroup (Fin n)), Function.Surjective ψ ∧ Nat.card ψ.ker = 3 := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := hD
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _), e.surjective.comp
    (QuotientGroup.mk'_surjective _), ?_⟩
  have : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center D))).ker =
      Subgroup.center D := by
    ext x
    simp
  rw [this, hZ]


theorem exists_image_triple (h : IsGoldschmidtTriple G₁ G₂) (hns : ¬ Group.IsSolvable D)
    {Y : Type*} [Group Y] (ψ : D →* Y) (hψ : Function.Surjective ψ) (hker : Nat.card ψ.ker = 3) :
    ∃ H₁ H₂ : Subgroup Y, IsGoldschmidtTriple H₁ H₂ ∧ Nonempty (↥H₁ ≃* ↥G₁) ∧
      Nonempty (↥H₂ ≃* ↥G₂) := by
  obtain ⟨hi₁, hi₂, htr⟩ := goldschmidtTriple_map_quotient_of_card_eq_three h hns hker
  let ε : D ⧸ ψ.ker ≃* Y := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  exact ⟨_, _, goldschmidtTriple_map_mulEquiv htr ε,
    ⟨((G₁.map (QuotientGroup.mk' ψ.ker)).equivMapOfInjective ε.toMonoidHom ε.injective).symm.trans
      (mulEquivMapOfInjOn _ hi₁).symm⟩,
    ⟨((G₂.map (QuotientGroup.mk' ψ.ker)).equivMapOfInjective ε.toMonoidHom ε.injective).symm.trans
      (mulEquivMapOfInjOn _ hi₂).symm⟩⟩

theorem image_triple_mulEquiv (h : IsGoldschmidtTriple G₁ G₂) {Y : Type*} [Group Y]
    (ε : D ≃* Y) :
    IsGoldschmidtTriple (G₁.map ε.toMonoidHom) (G₂.map ε.toMonoidHom) ∧
      Nonempty (↥(G₁.map ε.toMonoidHom) ≃* ↥G₁) ∧ Nonempty (↥(G₂.map ε.toMonoidHom) ≃* ↥G₂) ∧
      Nonempty (↥(G₁.map ε.toMonoidHom ⊓ G₂.map ε.toMonoidHom) ≃* ↥(G₁ ⊓ G₂)) :=
  ⟨goldschmidtTriple_map_mulEquiv h ε,
    ⟨(G₁.equivMapOfInjective ε.toMonoidHom ε.injective).symm⟩,
    ⟨(G₂.equivMapOfInjective ε.toMonoidHom ε.injective).symm⟩,
    ⟨((MulEquiv.subgroupCongr (Subgroup.map_inf_eq _ _ _ ε.injective)).symm.trans
      ((G₁ ⊓ G₂).equivMapOfInjective ε.toMonoidHom ε.injective).symm)⟩⟩

theorem dihedral_twelve_order_six : (DihedralGroup.r (2 : ZMod 12)) ^ 6 = 1 ∧
    (DihedralGroup.r (2 : ZMod 12)) ^ 2 ≠ 1 ∧ (DihedralGroup.r (2 : ZMod 12)) ^ 3 ≠ 1 :=
  dihedral_twelve_facts'.2.2.2

theorem dihedral_twelve_order_twelve : (DihedralGroup.r (1 : ZMod 12)) ^ 12 = 1 ∧
    (DihedralGroup.r (1 : ZMod 12)) ^ 4 ≠ 1 ∧ (DihedralGroup.r (1 : ZMod 12)) ^ 6 ≠ 1 :=
  ⟨dihedral_twelve_facts'.1, dihedral_twelve_facts'.2.1, dihedral_twelve_facts'.2.2.1⟩

theorem ne_two_of_pow_mod_sixteen {p e : ℕ} (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hpe : p ^ e % 16 = 7 ∨ p ^ e % 16 = 9) : p ≠ 2 := by
  rintro rfl
  interval_cases e <;> simp at hpe

section Cases

variable (I : F618QSInputs)
include I

theorem caseII (h : IsGoldschmidtTriple G₁ G₂) (hS : F618RecogSetting D)
    (ho : IsGoldCaseII G₁ G₂) : IsF618CaseFour G₁ G₂ := by
  obtain ⟨⟨e₁⟩, ⟨eT⟩, ⟨e₂⟩⟩ := ho
  obtain ⟨p, hp, hp8, hL⟩ := I.recogE4 D hS (exists_sylow_of_inf h eT)
  refine ⟨⟨p, hp, ?_, hL⟩, ⟨eT⟩, ⟨e₁⟩, ⟨e₂⟩⟩
  obtain ⟨-, K, _, _, hK, ⟨ε⟩⟩ := hL
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hD := (l2DicksonFacts_of_dickson I.dickson) p 1 K hp hp2 le_rfl hK
    (G₁.map ε.toMonoidHom)
  have h12 := hD.1 ⟨(G₁.equivMapOfInjective ε.toMonoidHom ε.injective).symm.trans e₁⟩
  rw [pow_one] at h12
  omega

theorem caseD8 (h : IsGoldschmidtTriple G₁ G₂) (hS : F618RecogSetting D)
    (eT : ↥(G₁ ⊓ G₂) ≃* DihedralGroup 4)
    (hty : IsGoldCaseIII G₁ G₂ ∨ IsGoldCaseIV G₁ G₂ ∨
      (Nonempty (↥G₁ ≃* Equiv.Perm (Fin 4)) ∧ Nonempty (↥G₂ ≃* Equiv.Perm (Fin 4)))) :
    IsF618CaseFive G₁ G₂ ∨ IsF618CaseSix G₁ G₂ ∨ IsF618CaseSeven G₁ G₂ := by
  have hns := not_isSolvable_of_setting hS
  rcases I.recogD8 D hS (exists_sylow_of_inf h eT) with
    ⟨p, e, hp, he1, he2, hpe, hL⟩ | hHat6 | ⟨q, hq, hq8, hPGL⟩ | he7 | hHat7
  ·
    have hp2 := ne_two_of_pow_mod_sixteen he1 he2 hpe
    obtain ⟨-, K, _, _, hK, ⟨ε⟩⟩ := id hL
    have hD := l2DicksonFacts_of_dickson I.dickson p e K hp hp2 he1 hK
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

theorem caseZ2D8 (h : IsGoldschmidtTriple G₁ G₂) (hS : F618RecogSetting D)
    (eT : ↥(G₁ ⊓ G₂) ≃* Multiplicative (ZMod 2) × DihedralGroup 4)
    (e₁ : ↥G₁ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))
    (hty : Nonempty (↥G₂ ≃* Equiv.Perm (Fin 3) × DihedralGroup 4) ∨
      Nonempty (↥G₂ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) :
    IsF618CaseEightCat G₁ G₂ ∨ IsF618CaseNineCat G₁ G₂ := by
  have hns := not_isSolvable_of_setting hS
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

theorem caseG22Prime (h : IsGoldschmidtTriple G₁ G₂) (hS : F618RecogSetting D)
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

theorem caseG22M12 (h : IsGoldschmidtTriple G₁ G₂) (hS : F618RecogSetting D)
    (ho : IsGoldCaseG22 G₁ G₂ ∨ IsGoldCaseM12 G₁ G₂) :
    IsF618CaseEleven G₁ G₂ ∨ IsF618CaseTwelve G₁ G₂ := by
  have hrec := I.recogG22M12 D G₁ G₂ hS h ho
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

theorem caseAutM12 (h : IsGoldschmidtTriple G₁ G₂) (hS : F618RecogSetting D)
    (ho : IsGoldCaseAutM12Cat G₁ G₂) : IsF618CaseThirteen G₁ G₂ := by
  have hD := I.recogAutM12 D G₁ G₂ hS h ho
  obtain ⟨⟨W, _, _, K₁, K₂, hW, hTL, φ₁, φ₂, hag₁, hag₂⟩, -, hq₁, hq₂, hext, hc₁, hz₁, hc₂⟩ := ho
  obtain ⟨aT, a₂⟩ := I.shapeAutM12 W K₁ K₂ hW hTL (quotientPCoreIsL22_of_mulEquiv φ₁ hq₁)
    (quotientPCoreIsL22_of_mulEquiv φ₂ hq₂)
    (isExtensionWith_centralProduct_of_mulEquiv φ₁.symm hext)
    (by rw [← Nat.card_congr (pCoreOfCongr φ₁).toEquiv]; exact hc₁)
    (by rw [← card_centerOf_eq (pCoreOfCongr φ₁)]; exact hz₁)
    (by rw [← Nat.card_congr (pCoreOfCongr φ₂).toEquiv]; exact hc₂)
  exact ⟨hD, isExtensionOf_of_mulEquiv (infMulEquivOfAmalgamIso φ₁ φ₂ hag₁ hag₂) aT, hext,
    isExtensionOf₃_of_mulEquiv φ₂ a₂⟩

theorem isF618CaseOrientedCat_of_oriented (h : IsGoldschmidtTriple G₁ G₂)
    (hS : F618RecogSetting D) (ho : IsGoldCaseOrientedCat G₁ G₂) :
    IsF618CaseOrientedCat G₁ G₂ := by
  unfold IsF618CaseOrientedCat
  rcases ho with hI | hII | hIII | hIV | hV | hVI
  · exact absurd (false_of_isGoldCaseI h hS.quasisimple hI) not_false
  · exact Or.inr (Or.inr (Or.inr (Or.inl (caseII I h hS hII))))
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

theorem f618QuasisimpleCaseCat_of (I : F618QSInputs) : F618QuasisimpleCaseCat := by
  intro D _ _ G₁ G₂ h hX hF hL
  have hS := f618RecogSetting_of I.theoremC hX hF hL
  obtain ⟨X, _, _, -, ⟨e⟩⟩ := hX
  have hA : IsGoldschmidtAmalgam G₁ G₂ := ⟨h, (remark_f6_15 e).2⟩
  rcases I.goldschmidt D G₁ G₂ hA with ho | ho
  · exact Or.inl (isF618CaseOrientedCat_of_oriented I h hS ho)
  · exact Or.inr (isF618CaseOrientedCat_of_oriented I h.symm hS ho)

theorem theoremF618Cat_of (hNQ : F617NonquasisimpleCaseCat) (I : F618QSInputs) :
    TheoremF618Cat :=
  theoremF618Cat_of_cases hNQ (f618QuasisimpleCaseCat_of I)

end F6

end CFSG.Quasithin
