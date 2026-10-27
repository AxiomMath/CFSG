module

public import CFSG.Quasithin.Background.SmithC27RTypeI

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin


variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

theorem residueTypeII_of_ne (hC124 : C124StatementSQTK (G := G)) (h : Hyp27 H R M K)
    (hs : StarHyp R K V) (hnchi : ¬ IsChiBlock2 H K) (hnexc : ¬ IsExcA7Block K)
    (hV : IsElemAbelian 2 V) (hHyp : B51Hyp (jPStar hV R K) (autI hV K))
    (hGL : jPStar hV R K ≠ autI hV K)
    (halt : ∀ T, IsSylowTwoOf T (jPStar hV R K) → (jPStar hV R K = autI hV K ∨
      (jPStar hV R K = autI hV K ⊔ T ∧
        ((∃ n, 5 ≤ n ∧ n ≤ 8 ∧ SymmetricNatural (jPStar hV R K) (commV (autI hV K))
            (fixV (autI hV K) ⊓ commV (autI hV K)) n) ∨
          G2Natural (jPStar hV R K) (commV (autI hV K))
            (fixV (autI hV K) ⊓ commV (autI hV K)) 1)))) :
    ResidueTypeII R K V := by
  have hLG : autI hV K ≤ jPStar hV R K := B5.le_G hHyp
  have hall : ∀ T, IsSylowTwoOf T (jPStar hV R K) → jPStar hV R K = autI hV K ⊔ T :=
    fun T hT => ((halt T hT).resolve_left hGL).1
  obtain ⟨T, hT⟩ := B5.exists_isSylowTwoOf (jPStar hV R K)
  have hmod := ((halt T hT).resolve_left hGL).2
  have hLn : ((autI hV K).subgroupOf (jPStar hV R K)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using B5.normal_L hHyp g g.2 n hn⟩
  have hq : CFSG.IsQuasisimple ↥(autI hV K) := B5.quasi_L hHyp
  have hLperf : ⁅autI hV K, autI hV K⁆ = autI hV K := Subgroup.isPerfect_iff.1 hq.1
  have hLperf' : ⁅(autI hV K).subgroupOf (jPStar hV R K),
      (autI hV K).subgroupOf (jPStar hV R K)⁆ = (autI hV K).subgroupOf (jPStar hV R K) := by
    apply Subgroup.map_injective (jPStar hV R K).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLG, hLperf]
  have hL1 : (autI hV K).subgroupOf (jPStar hV R K) ≠ ⊥ := by
    intro hb
    have hL0 : autI hV K = ⊥ := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hLG, hb, Subgroup.map_bot]
    exact (Subgroup.nontrivial_iff_ne_bot _).1 (FFC.nontrivial_of_isQuasisimple hq) hL0
  refine ⟨hV, thompsonJ_le_jPStar hs hV, hall, ?_⟩
  rcases hmod with ⟨n, hn5, hn8, π, hπ⟩ | ⟨F, iF, fF, hF, π, hπ⟩
  · let π' : Equiv.Perm (Fin n) →* ↥(jPStar hV R K) := π
    have hinj : Function.Injective π' :=
      FFC.injective_of_faithful_sec (FFC.symDn_faithful hn5) hπ
    have heq := eq_map_alternatingGroup hn5 π' ⟨hinj, hπ.1⟩ hLn hLperf' hL1
    have hmem : ∀ σ : Equiv.Perm (Fin n),
        ((π' σ : ↥(jPStar hV R K)) : MulAut (IntMod V hV)) ∈ autI hV K ↔
          σ ∈ alternatingGroup (Fin n) := by
      intro σ
      rw [← Subgroup.mem_subgroupOf, heq, Subgroup.mem_map_iff_mem hinj]
    let e : ↥(alternatingGroup (Fin n)) ≃* ↥(autI hV K) :=
      ((Subgroup.equivMapOfInjective _ π' hinj).trans (MulEquiv.subgroupCongr heq.symm)).trans
        (Subgroup.subgroupOfEquivOfLe hLG)
    have hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases hn with rfl | rfl | rfl | rfl
    · exact (false_of_autOn_equiv_alt hC124 h hs hnchi hnexc (Or.inl rfl) e.symm).elim
    · exact Or.inl ⟨6, Or.inl rfl, π, hπ, hmem⟩
    · exact (false_of_autOn_equiv_alt hC124 h hs hnchi hnexc (Or.inr rfl) e.symm).elim
    · exact Or.inl ⟨8, Or.inr rfl, π, hπ, hmem⟩
  · have : CharP F 2 := FFC.charP_two_of_card_pow hF
    have hF2 : Nat.card F = 2 := hF.trans (pow_one 2)
    let π' : ↥(quasithinG2 F) →* ↥(jPStar hV R K) := π
    have hinj : Function.Injective π' :=
      FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ
    have heq := eq_map_g2Derived hF2 π' ⟨hinj, hπ.1⟩ hLn hLperf' hL1
    refine Or.inr ⟨F, iF, fF, hF2, π', hπ, fun g => ?_⟩
    rw [← Subgroup.mem_subgroupOf, heq, Subgroup.mem_map_iff_mem hinj, Subgroup.mem_subgroupOf]

theorem residue_cases (hA21 : AsA21SQTKSection) (hB51 : AsB51) (hI : B5.B51IrrInputs)
    (hC124 : C124StatementSQTK (G := G)) (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hnchi : ¬ IsChiBlock2 H K) (hnexc : ¬ IsExcA7Block K) :
    (autOn (thompsonJ R) V ≤ autOn K V ∧ ResidueTypeI K V) ∨ ResidueTypeII R K V := by
  have hV := hs.elemAbelian
  obtain ⟨-, -, -, hHyp, hC, -⟩ := moduleType_of h hs hV hA21 hB51
  have hJ := thompsonJ_le_jPStar hs hV
  obtain ⟨⟨-, hcases⟩, -⟩ := hC
  rcases hcases with ⟨hU, hpair, halt⟩ | hii | ⟨m, hiii⟩ | hiv
  · by_cases hGL : jPStar hV R K = autI hV K
    · exact Or.inl ⟨hJ.trans hGL.le,
        residueTypeI_of_pair hI hC124 h hs hnchi hnexc hV hHyp hGL hU hpair⟩
    · exact Or.inr (residueTypeII_of_ne hC124 h hs hnchi hnexc hV hHyp hGL halt)
  · exact Or.inl ⟨hJ.trans hii.1.le, residueTypeI_of_case1ii hV hii⟩
  · exact Or.inl ⟨hJ.trans hiii.1.le, residueTypeI_of_case1iii hV hiii⟩
  · exact Or.inl ⟨hJ.trans hiv.1.le, residueTypeI_of_case1iv hV hiv⟩

end CFSG.Quasithin.SmithC27
