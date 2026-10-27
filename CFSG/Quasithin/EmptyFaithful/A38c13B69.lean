module

public import CFSG.Quasithin.Background.B69SL3
public import CFSG.Quasithin.Background.E2TwoNoNStmt
public import CFSG.Quasithin.Background.B69E22Pre
public import CFSG.Quasithin.Background.B69Final
public import CFSG.Quasithin.Background.B69Simple

public section

namespace CFSG.Quasithin

section Num

open CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.ClassicalOrders

namespace B69

theorem e22CasesNoN_fam {Γ : Type} [Group Γ] {H T M K : Subgroup Γ} (h : E2.E22CasesNoN H T M K) :
    E22Fam ↥(E2.star M H K) := by
  unfold E2.E22CasesNoN at h
  dsimp only at h
  rcases h with ⟨-, t, -, -, -, h1⟩ | ⟨-, -, h2⟩
  · rcases h1 with ⟨n, -, h1 | h1, -⟩ | ⟨p, -, -, h1, -⟩
    · exact Or.inl ⟨2, n, h1⟩
    · exact Or.inr (Or.inl ⟨n, h1⟩)
    · exact Or.inl ⟨p, 1, h1⟩
  · rcases h2 with ⟨n, ⟨-, h2 | h2 | h2⟩, -⟩ | ⟨n, hn, h2 | h2, -⟩ | ⟨p, e, -, -, -, -, h2, -⟩ |
        ⟨p, -, hp2, h2 | h2, -⟩
    · exact Or.inl ⟨2, n, h2⟩
    · exact Or.inr (Or.inl ⟨n, h2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨n, h2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h2⟩))))
    · exact Or.inl ⟨p, e, h2⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp2, h2.2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp2, h2.2.1⟩)))))

end B69

end Num

section Link

open CFSG.Open CFSG.QuasithinUnique B6
open scoped commutatorElement

namespace B69

variable {H₀ Y : Type} [Group H₀] [Group Y]

theorem exists_quotient_e22NoN
    (h22 : E2.E22StatementNoN) [Finite H₀] [Finite Y] {S M : Subgroup Y}
    (hmp : MinParabolic (⊤ : Subgroup Y) S M) (hH₀ : SQTKGroup H₀) (φ : H₀ →* Y)
    (hφ : Function.Surjective φ) {L : Subgroup Y} (hL : CFSG.Open.IsComponentOf L ⊤) :
    ∃ (F : Type) (_ : Group F) (π : ↥L →* F), Function.Surjective π ∧ E22Fam F := by
  classical
  obtain ⟨H, T, M', hmp', hHmap, hTS, hM'M, hkerH⟩ := exists_minParabolic_preimage φ hφ hmp
  have hMH : M' ≤ H := hmp'.maximal.1.le
  have hsq : SQTKGroup ↥H := ⟨sqt_subgroup hH₀.1 H, kGroup_subgroup hH₀.2 H⟩
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLperf : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hLq.1
  have hLnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLq
  have hYns : ¬ Group.IsSolvable Y := fun hY => by
    have : Group.IsSolvable ↥L := Group.isSolvable_of_isSolvable_injective (f := L.subtype)
      L.subtype_injective
    exact Group.IsPerfect.not_isSolvable ↥L this
  have hφH : Function.Surjective (φ.comp H.subtype) := by
    intro y
    have : y ∈ H.map φ := by rw [hHmap]; trivial
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  have hHns : ¬ Group.IsSolvable ↥H := fun hHs => hYns (Group.isSolvable_of_surjective hφH)
  obtain ⟨⟨K, hKc, hHK, -, hcases⟩, -⟩ := h22 H₀ H T M' hmp' hsq hHns
  set J : Subgroup Y := kerIn M ⊤ with hJ
  let f : ↥H →* Y ⧸ J := (QuotientGroup.mk' J).comp (φ.comp H.subtype)
  have hfs : Function.Surjective f := (QuotientGroup.mk'_surjective J).comp hφH
  have hfker : f.ker = (kerIn M' H).subgroupOf H := ker_star_hom φ hMH hHmap hM'M hkerH
  let ψ : E2.StarQuot M' H ≃* Y ⧸ J :=
    (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs)
  have hψ : ∀ x : ↥H, ψ (QuotientGroup.mk x) = f x := fun x => rfl
  let Kh : Subgroup (Y ⧸ J) := (K.subgroupOf H).map f
  have hKh : (E2.star M' H K).map ψ.toMonoidHom = Kh := by
    show ((K.subgroupOf H).map (QuotientGroup.mk' _)).map ψ.toMonoidHom = _
    rw [Subgroup.map_map]
    refine congrArg (fun g => (K.subgroupOf H).map g) ?_
    ext x
    rfl
  have hfam : E22Fam ↥(E2.star M' H K) := e22CasesNoN_fam hcases
  have e1 : ↥(E2.star M' H K) ≃* ↥Kh :=
    (Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).trans (MulEquiv.subgroupCongr hKh)
  have hfamK : E22Fam ↥Kh := hfam.congr e1
  have hKs : IsSimpleGroup ↥Kh := hfamK.isSimpleGroup
  have hKsn : (K.subgroupOf H).IsSubnormal :=
    isSubnormal_subgroupOf_of_chain (subnormal_of_mem_cComp hKc)
  have hKhsn : Kh.IsSubnormal := hKsn.map hfs
  let Th : Subgroup (Y ⧸ J) := (T.subgroupOf H).map f
  have hTH : T ≤ H := hmp'.isSylow.1
  have hKH : K ≤ H := hHK ▸ le_sup_left
  have hT2 : IsPGroup 2 ↥Th := by
    have hT2' : IsPGroup 2 ↥(T.subgroupOf H) :=
      hmp'.isSylow.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
    exact hT2'.map _
  have hsupH : K.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKH,
      Subgroup.map_subgroupOf_eq_of_le hTH, ← hHK, Subgroup.map_top, Subgroup.range_subtype]
  have hsup : Kh ⊔ Th = ⊤ := by
    show (K.subgroupOf H).map f ⊔ (T.subgroupOf H).map f = ⊤
    rw [← Subgroup.map_sup, hsupH, Subgroup.map_top, MonoidHom.range_eq_top.mpr hfs]
  have hJs : Group.IsSolvable ↥J := hmp.isSolvable_kerIn
  have hLf : ¬ L ≤ (QuotientGroup.mk' J).ker := by
    intro hle
    rw [QuotientGroup.ker_mk'] at hle
    have : Group.IsSolvable ↥L := Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    exact Group.IsPerfect.not_isSolvable ↥L this
  have hLb := isComponentOf_map_top (QuotientGroup.mk' J) (QuotientGroup.mk'_surjective J) hL hLf
  obtain ⟨z, hz⟩ := exists_conj_eq_of_component hLb hKhsn hKs hT2 hsup
  have e2 : ↥Kh ≃* ↥(L.map (QuotientGroup.mk' J)) :=
    (Kh.equivMapOfInjective (MulAut.conj z).toMonoidHom (MulAut.conj z).injective).trans
      (MulEquiv.subgroupCongr hz.symm)
  refine ⟨↥(L.map (QuotientGroup.mk' J)), inferInstance,
    (QuotientGroup.mk' J).subgroupMap L, (QuotientGroup.mk' J).subgroupMap_surjective L, ?_⟩
  exact hfamK.congr e2

end B69

end Link

section Main

open CFSG.Assembly.LowTwoRank

namespace B69

theorem no_component_slNoN
    (h22 : E2.E22StatementNoN) {H₀ Y : Type} [Group H₀] [Finite H₀] [Group Y]
    [Finite Y] {S M : Subgroup Y} (hmp : MinParabolic (⊤ : Subgroup Y) S M) (hH₀ : SQTKGroup H₀)
    (φ : H₀ →* Y) (hφ : Function.Surjective φ) {L : Subgroup Y}
    (hL : CFSG.Open.IsComponentOf L ⊤) {n : ℕ} (hn : n = 4 ∨ n = 5) {K : Type} [Field K]
    (hK : Nat.card K = 2) {Q : Type} [Group Q] (ℓ : ↥L →* Q) (hℓ : Function.Surjective ℓ)
    (e : Q ≃* ↥(StatedSL n K)) : False := by
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  obtain ⟨F, _, π, hπ, hfam⟩ := exists_quotient_e22NoN h22 hmp hH₀ φ hφ hL
  have hFs : IsSimpleGroup F := hfam.isSimpleGroup
  have hQs : IsSimpleGroup Q :=
    (MulEquiv.isSimpleGroup_congr e).mpr (isSimpleGroup_statedSL_two hK (by omega))
  obtain ⟨eFQ⟩ := equiv_of_central_quotients hL.2.2 π hπ ℓ hℓ
  have eFS : F ≃* ↥(StatedSL n K) := eFQ.trans e
  rcases hn with rfl | rfl
  · have hcard : Nat.card F = 20160 := by
      rw [Nat.card_congr eFS.toEquiv]
      exact card_statedSL_two_four hK
    obtain ⟨F', _, _, hF', ⟨e3⟩⟩ := hfam.exists_psl_three_four hcard
    exact not_equiv_sl_four_psl_three hK hF' (eFS.trans (statedSLEquivStatedProj hK 4)) e3
  · have hcard : Nat.card F = 9999360 := by
      rw [Nat.card_congr eFS.toEquiv]
      exact card_statedSL_two_five hK
    exact hfam.card_ne hcard

theorem noStrongLn_of_E22NoN
    (h22 : E2.E22StatementNoN) : AsB69NoStrongLn := by
  intro V _ _ hV X S M A L hdata hcase
  obtain ⟨⟨H₀, _, _, hsq, hkg, φ, hφ⟩, hmp, hO2, hA, hAs, hL, hLA⟩ := hdata
  obtain ⟨n, K, _, _, Q, _, ℓ, hℓ, hn, hK, ⟨e⟩⟩ := sectionHas_case9 hcase
  have e0 : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hL.1
  exact no_component_slNoN h22 hmp ⟨hsq, hkg⟩ φ hφ (isComponentOf_subgroupOf hL) hn hK
    (ℓ.comp e0.toMonoidHom) (hℓ.comp e0.surjective) e

theorem noStrongS8_of_E22NoN
    (h22 : E2.E22StatementNoN) : AsB69NoStrongS8 := by
  intro V _ _ hV X S M A L hdata hcase
  obtain ⟨⟨H₀, _, _, hsq, hkg, φ, hφ⟩, hmp, hO2, hA, hAs, hL, hLA⟩ := hdata
  obtain ⟨Q, _, ℓ, hℓ, ⟨e⟩⟩ := sectionHas_case10ii hcase
  have e0 : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hL.1
  exact no_component_slNoN h22 hmp ⟨hsq, hkg⟩ φ hφ (isComponentOf_subgroupOf hL) (Or.inl rfl)
    (K := ZMod 2) (by simp) (ℓ.comp e0.toMonoidHom) (hℓ.comp e0.surjective) e

theorem b69One_of_E22NoN
    (h42 : AsB42) (hP4 : AsB15Part4) (hA21 : AsA21SQTKSection)
    (h22 : E2.E22StatementNoN) (hSL3 : AsB69NoStrongSL3) (hSp4 : AsB69NoStrongSp4) : B69One :=
  b69One_of_inputs h42 hP4 hA21 ⟨hSL3, hSp4, noStrongLn_of_E22NoN h22, noStrongS8_of_E22NoN h22⟩

end B69

end Main

section SL3

open CFSG.Assembly.LowTwoRank H H.SL3Pair
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open B6

namespace B69

theorem b69One_of_Sp4NoN
    (h42 : AsB42) (hP4 : AsB15Part4) (hA21 : AsA21SQTKSection)
    (h22 : E2.E22StatementNoN) (hSp4 : AsB69NoStrongSp4) : B69One :=
  b69One_of_E22NoN h42 hP4 hA21 h22 noStrongSL3 hSp4

end B69

end SL3

end CFSG.Quasithin
