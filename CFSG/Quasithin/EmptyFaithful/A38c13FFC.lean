module

public import CFSG.Quasithin.EmptyFaithful.A38c13B69
public import CFSG.Quasithin.Background.FFC13F
public import CFSG.Quasithin.Background.FFC11C
public import CFSG.Quasithin.Background.FFC11E
public import CFSG.Quasithin.Background.FFC11G
public import CFSG.Quasithin.Background.FFC12F
public import CFSG.Quasithin.Background.FFC13A
public import CFSG.Quasithin.Background.FFC13B
public import CFSG.Quasithin.Background.FFC13D
public import CFSG.Quasithin.Background.FFC13E
public import CFSG.Quasithin.Background.FFC13S

public section

namespace CFSG.Quasithin

section Cases

open CFSG.Open
open scoped commutatorElement

namespace B69

section Section

variable {V : Type} [CommGroup V] [Finite V]

theorem false_of_sl_sectionNoN (h22 : E2.E22StatementNoN)
    {X T M A L : Subgroup (MulAut V)} (hH : CompHyp X T M A L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) {n : ℕ} (hn : n = 4 ∨ n = 5) {K : Type} [Field K]
    (hK : Nat.card K = 2) (π : ↥(CFSG.Assembly.LowTwoRank.StatedSL n K) →* ↥(wtL L W)) (hπ : Function.Surjective π) : False := by
  obtain ⟨⟨H₀, _, _, hsq, hkg, φ, hφ⟩, hmp, hO2, -, -, -, hL, -⟩ := hH
  obtain ⟨hLW, hLZ⟩ := stab_of_irr hW
  obtain ⟨ℓ, hℓs, -⟩ := exists_surj_autSec hLW hLZ
  have hs : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL n K) := isSimpleGroup_statedSL_two hK (by omega)
  have hnt : Nontrivial ↥(wtL L W) := nontrivial_autSec hW
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro g hg
    rcases CFSG.eq_bot_or_eq_top_of_normal π.ker (MonoidHom.normal_ker π) with hbot | htop
    · have : g ∈ π.ker := MonoidHom.mem_ker.2 hg
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    · exfalso
      obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
      obtain ⟨x, rfl⟩ := hπ a
      obtain ⟨y, rfl⟩ := hπ b
      apply hab
      have hx : x ∈ π.ker := by rw [htop]; trivial
      have hy : y ∈ π.ker := by rw [htop]; trivial
      rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy]
  have e0 : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hL.1
  exact no_component_slNoN h22 hmp.subgroupOf ⟨hsq, hkg⟩ φ hφ (isComponentOf_subgroupOf hL) hn hK
    (ℓ.comp e0.toMonoidHom) (hℓs.comp e0.surjective) (MulEquiv.ofBijective π ⟨hinj, hπ⟩).symm

end Section

theorem asB69Component_of_named_inputsNoN (h22 : E2.E22StatementNoN)
    (hb42 : AsB69SectionB42) (hsl3 : AsB69NoRankTwoSL3) (ha7 : AsB69NoA7)
    (hD3 : AsB69NoOddCoverSL2) (hin : AsB69DeepInputs) : AsB69Component := by
  intro V _ _ hV X T M A L hH W hW
  obtain ⟨B, hBA, hBoff, hconcl⟩ := hb42 V hV X T M A L hH W hW
  have hO2 : pCoreOf 2 X = ⊥ := hH.2.2.1
  have hL : CFSG.Open.IsComponentOf L X := hH.2.2.2.2.2.2.1
  rcases hconcl with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11
  · have hnat := binaryNaturalSL_of_case1 hD3 hO2 hL hW c1.2.1
    exact Or.inl ⟨hnat, hin.oneSylow V hV X T M A L hH W hW hnat,
      hin.oneBorel V hV X T M A L hH W hW hnat⟩
  · exact (hsl3 V hV X T M A L hH W hW c2).elim
  · exact (hin.sp4 V hV X T M A L hH W hW c3).elim
  · exact (hin.g2 V hV X T M A L hH W hW B hBA hBoff c4).elim
  · exact Or.inr (hin.alt V hV X T M A L hH W hW B hBA hBoff c5)
  · exact (hin.a6 V hV X T M A L hH W hW B hBA hBoff c6).elim
  · exact (ha7 V hV X T M A L hH W hW B hBA hBoff c7).elim
  · exact (hin.tripleA6 V hV X T M A L hH W hW B hBA hBoff c8).elim
  · obtain ⟨-, n, hn, ⟨K, hKf, hKfin, hK, π, hπ⟩, -⟩ := c9
    exact (false_of_sl_sectionNoN h22 hH hW hn (by simpa using hK) π hπ.1).elim
  · obtain ⟨⟨π, hπ⟩, -⟩ := c10
    exact (false_of_sl_sectionNoN h22 hH hW (Or.inl rfl) (K := ZMod 2) (by simp) π hπ.1).elim
  · obtain ⟨-, -, -, -, π, hπ, -⟩ := c11
    exact (false_of_sl_sectionNoN h22 hH hW (Or.inr rfl) (K := ZMod 2) (by simp) π hπ.1).elim

end B69

end Cases

namespace B69

theorem asB69Component_of_inputsNoN (h22 : E2.E22StatementNoN)
    (hb42 : AsB69SectionB42) (hsl3 : AsB69NoRankTwoSL3) (ha7 : AsB69NoA7)
    (hin : AsB69DeepInputs) : AsB69Component :=
  asB69Component_of_named_inputsNoN h22 hb42 hsl3 ha7 asB69NoOddCoverSL2 hin

end B69

section A7

open CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.ClassicalOrders
open scoped commutatorElement

namespace B69

theorem noA7_ofNoN (h22 : E2.E22StatementNoN) {V : Type} [CommGroup V]
    [Finite V] {X T M A L : Subgroup (MulAut V)} (hH : CompHyp X T M A L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V))
    {B : Subgroup (MulAut (Sec W (W ⊓ fixV L)))}
    (hc : B42Case7 (autSec (L ⊔ A) W (W ⊓ fixV L)) (autSec L W (W ⊓ fixV L)) B) : False := by
  obtain ⟨⟨H₀, _, _, hsq, hkg, φ, hφ⟩, hmp, hO2, -, -, -, hL, -⟩ := hH
  obtain ⟨-, -, ⟨α, π, hπ⟩, -, -, -⟩ := hc
  obtain ⟨hLW, hLZ⟩ := stab_of_irr hW
  obtain ⟨ℓ, hℓs, -⟩ := exists_surj_autSec hLW hLZ
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hs' : IsSimpleGroup (FFModel.a7Four α).Gam := hs
  have hnt : Nontrivial ↥(autSec L W (W ⊓ fixV L)) := nontrivial_autSec hW
  have hπs : Function.Surjective π := hπ.1
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro g hg
    rcases CFSG.eq_bot_or_eq_top_of_normal π.ker (MonoidHom.normal_ker π) with hbot | htop
    · have : g ∈ π.ker := MonoidHom.mem_ker.2 hg
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    · exfalso
      obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
      obtain ⟨x, rfl⟩ := hπs a
      obtain ⟨y, rfl⟩ := hπs b
      apply hab
      have hx : x ∈ π.ker := by rw [htop]; trivial
      have hy : y ∈ π.ker := by rw [htop]; trivial
      rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy]
  let e : ↥(autSec L W (W ⊓ fixV L)) ≃* ↥(alternatingGroup (Fin 7)) :=
    (MulEquiv.ofBijective π ⟨hinj, hπs⟩).symm
  have hQs : IsSimpleGroup ↥(autSec L W (W ⊓ fixV L)) := (MulEquiv.isSimpleGroup_congr e).mpr hs
  obtain ⟨F, _, πF, hπF, hfam⟩ := exists_quotient_e22NoN h22 hmp.subgroupOf ⟨hsq, hkg⟩ φ hφ
    (isComponentOf_subgroupOf hL)
  have hFs : IsSimpleGroup F := hfam.isSimpleGroup
  have e0 : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hL.1
  obtain ⟨eFQ⟩ := equiv_of_central_quotients (isComponentOf_subgroupOf hL).2.2 πF hπF
    (ℓ.comp e0.toMonoidHom) (hℓs.comp e0.surjective)
  have hcard : Nat.card F = 2520 := by
    rw [Nat.card_congr (eFQ.trans e).toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  exact hfam.card_ne_2520 hcard

end B69

end A7

namespace B69

theorem asB69NoA7_provedNoN (h22 : E2.E22StatementNoN) : AsB69NoA7 :=
  fun _ _ _ _ _ _ _ _ _ hH _ hW _ _ _ hc => noA7_ofNoN h22 hH hW hc

theorem asB69Component_of_deep_inputsNoN (hB42 : AsB42)
    (hA21 : AsA21SQTKSection) (h22 : E2.E22StatementNoN) (hdeep : AsB69DeepInputs) :
    AsB69Component :=
  asB69Component_of_inputsNoN h22 (asB69SectionB42_of hB42 hA21) asB69NoRankTwoSL3_proved
    (asB69NoA7_provedNoN h22) hdeep

theorem asB69Component_of_deep_inputs_restNoN (hB42 : AsB42)
    (hA21 : AsA21SQTKSection) (h22 : E2.E22StatementNoN) (hdeep : AsB69DeepInputsRest) :
    AsB69Component :=
  asB69Component_of_deep_inputsNoN hB42 hA21 h22 hdeep.toDeep

end B69

section Alt

open CFSG.Open
open scoped commutatorElement

namespace B69

section Section

variable {V : Type} [CommGroup V] [Finite V]

theorem false_of_alt_sevenNoN (h22 : E2.E22StatementNoN)
    {X T M A L : Subgroup (MulAut V)} (hH : CompHyp X T M A L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V))
    (e : ↥(wtL L W) ≃* ↥(alternatingGroup (Fin 7))) : False := by
  obtain ⟨⟨H₀, _, _, hsq, hkg, φ, hφ⟩, hmp, hO2, -, -, -, hL, -⟩ := hH
  obtain ⟨hLW, hLZ⟩ := stab_of_irr hW
  obtain ⟨ℓ, hℓs, -⟩ := exists_surj_autSec hLW hLZ
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hQs : IsSimpleGroup ↥(wtL L W) := (MulEquiv.isSimpleGroup_congr e).mpr hs
  obtain ⟨F, _, πF, hπF, hfam⟩ := exists_quotient_e22NoN h22 hmp.subgroupOf ⟨hsq, hkg⟩ φ hφ
    (isComponentOf_subgroupOf hL)
  have hFs : IsSimpleGroup F := hfam.isSimpleGroup
  have e0 : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hL.1
  obtain ⟨eFQ⟩ := equiv_of_central_quotients (isComponentOf_subgroupOf hL).2.2 πF hπF
    (ℓ.comp e0.toMonoidHom) (hℓs.comp e0.surjective)
  have hcard : Nat.card F = 2520 := by
    rw [Nat.card_congr (eFQ.trans e).toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  exact hfam.card_ne_2520 hcard

theorem case5_altNoN (h22 : E2.E22StatementNoN) (hA21 : AsA21SQTKSection)
    (hV : ∀ v : V, v ^ 2 = 1) {X T M A L : Subgroup (MulAut V)} (hH : CompHyp X T M A L)
    {W : Subgroup V} (hW : W ∈ IrrPlus L (⊤ : Subgroup V))
    {B : Subgroup (MulAut (Sec W (W ⊓ fixV L)))}
    (hc : B42Case5 (wtLA A L W) B) :
    ∃ π : Equiv.Perm (Fin 5) →* ↥(ffJ (wtLA A L W)),
      Function.Injective π ∧ Function.Surjective π ∧
      (FFModel.symDn 5).RealizesVia (ffJ (wtLA A L W)) ⊤ ⊥ π ∧
      wtL L W = (alternatingGroup (Fin 5)).map ((ffJ (wtLA A L W)).subtype.comp π) ∧
      ∃ T' : Set (Equiv.Perm (Fin 5)), (∀ t ∈ T', t.IsSwap) ∧ T'.Pairwise Commute ∧
        B.subgroupOf (ffJ (wtLA A L W)) = (Subgroup.closure T').map π := by
  obtain ⟨hB4, hLbn, hHb2⟩ := sectionData hA21 hV hH hW
  obtain ⟨⟨n, hn, π, hπ, T', hT'sw, hT'c, hBT⟩, -⟩ := hc
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hπi : Function.Injective π := FFC.injective_of_faithful_sec (FFC.symDn_faithful hn5) hπ
  have hπs : Function.Surjective π := hπ.1
  have hJG : ffJ (wtLA A L W) ≤ wtLA A L W := B6.ffJ_le _
  have hJn : ∀ g ∈ wtLA A L W, ∀ j ∈ ffJ (wtLA A L W), g * j * g⁻¹ ∈ ffJ (wtLA A L W) := by
    intro g hg j hj
    exact (Subgroup.mem_normalizer_iff.1 (B6.le_normalizer_ffJ _ hg) j).1 hj
  have hLG : wtL L W ≤ wtLA A L W := autSec_mono le_sup_left W _
  have hLq : CFSG.Open.IsQuasisimple ↥(wtL L W) := B1Red.isQuasisimple_to_open hB4.2.2.1
  have hLeq := wtL_eq_alt hn5 hπi hπs hJG hJn hLbn hHb2 hLG hLq
  rcases hn with rfl | rfl
  · exact ⟨π, hπi, hπs, hπ, hLeq, T', hT'sw, hT'c, hBT⟩
  · exfalso
    let ψ : Equiv.Perm (Fin 7) →* MulAut (Sec W (W ⊓ fixV L)) := (ffJ (wtLA A L W)).subtype.comp π
    have hψi : Function.Injective ψ := (ffJ (wtLA A L W)).subtype_injective.comp hπi
    let e1 : ↥(alternatingGroup (Fin 7)) ≃* ↥((alternatingGroup (Fin 7)).map ψ) :=
      Subgroup.equivMapOfInjective _ ψ hψi
    have e2 : ↥((alternatingGroup (Fin 7)).map ψ) ≃* ↥(wtL L W) := MulEquiv.subgroupCongr hLeq.symm
    exact false_of_alt_sevenNoN h22 hH hW (e1.trans e2).symm

end Section

theorem asB69AltCase_ofNoN (h22 : E2.E22StatementNoN)
    (hA21 : AsA21SQTKSection) : AsB69AltCase := by
  intro V _ _ hV X T M A L hH W hW B hBA hBo hc
  obtain ⟨-, hmp, hO2, -, -, hA, hL, hLA⟩ := id hH
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  obtain ⟨π, hπi, -, hπ, hLeq, T', hT'sw, -, hBT⟩ := case5_altNoN h22 hA21 hV hH hW hc
  have hU : W ⊓ fixV L = ⊥ := fixV_eq_bot_of_alt hV hLq hW π hπi hπ hLeq
  obtain ⟨hLW, hLZ⟩ := stab_of_irr hW
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  have hAW := a_stab_irr hV hA hLq hLA hW
  have hAWs : A ≤ stabSub W := B1.le_stabSub_of_invariant hAW
  have hAZs : A ≤ stabSub (W ⊓ fixV L) :=
    B1.le_stabSub_of_invariant (isInv_inf hAW (B1Red.fixV_inv_of_normalizes hAn))
  have hS2 : ∀ s : Sec W (W ⊓ fixV L), s ^ 2 = 1 := sq_eq_one_sec hV W (W ⊓ fixV L)
  have hq : qOf (wtLA A L W) = ((1 : ℚ) : WithTop ℚ) := hc.2
  have hnonstrong := section_nonstrong hV hH hW hq
  obtain ⟨hsup, hfaithA⟩ := eq_sup_fixV_of_sec hV hA hLq hLA hW hnonstrong
  have hnt : commSub W A ≠ ⊥ := commSub_ne_bot_of_irr hLA hW
  have hge := sec_card_le_of_offender hA.1 hLq hAn hW hAW hnt
  have hAprod : Nat.card (autSec A W (W ⊓ fixV L)) *
      Nat.card (fixV (autSec A W (W ⊓ fixV L))) = Nat.card (Sec W (W ⊓ fixV L)) :=
    le_antisymm hnonstrong hge
  have hBoff : IsFFStarOffender (autSec A W (W ⊓ fixV L)) B :=
    ⟨hBA, hBo.2.1, hBo.2.2.1, hBo.2.2.2⟩
  have hr1 : rAV B = 1 := rAV_eq_one_of_one_le_qOf hS2 (hq ▸ le_rfl) hBo
  have hBprod : Nat.card (Sec W (W ⊓ fixV L)) = Nat.card B * Nat.card (fixV B) :=
    (rAV_eq_one_iff hS2 hBo.isA2).1 hr1
  have hBeq : B = autSec A W (W ⊓ fixV L) :=
    lift_offender hA hU hAWs hAZs hsup hfaithA hBoff (hBprod.symm.trans hAprod.symm)
  obtain ⟨e, he⟩ := exists_core_equiv_top hπ
  have hBJ : B ≤ ffJ (wtLA A L W) := B6.le_ffJ hBo
  have hBψ : B = (Subgroup.closure T').map ((ffJ (wtLA A L W)).subtype.comp π) := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hBJ, hBT, Subgroup.map_map]
  obtain ⟨t, ht, hAeq⟩ := single_swap hA hU hAWs hAZs hsup hfaithA e _
    ((ffJ (wtLA A L W)).subtype_injective.comp hπi) he hBoff hBeq hAprod T' hT'sw hBψ
  have hGJ : wtLA A L W ≤ ffJ (wtLA A L W) := by
    show autSec (L ⊔ A) W (W ⊓ fixV L) ≤ _
    rw [autSec_sup_eq (sup_le hLW hAWs) (sup_le hLZ hAZs)]
    refine sup_le ?_ ?_
    · refine (le_of_eq hLeq).trans ?_
      rintro _ ⟨σ, -, rfl⟩
      exact (π σ).2
    · rw [← hBeq]
      exact hBJ
  have hJ : ffJ (wtLA A L W) = autSec (L ⊔ A) W (W ⊓ fixV L) := le_antisymm (B6.ffJ_le _) hGJ
  obtain ⟨π', hπ'i, hπ's, hπ'r, hLeq', i, j, hij, hAeq'⟩ := alt_data hV hO2 hA hL hLA hU hW hLZ
    hAZs hsup hJ π hπi hπ hLeq ht hAeq
  obtain ⟨hcV, hAcQ, -⟩ := commV_eq_of_sup hV hA hLq hLA hW hsup
  have hAc : ∀ L' : Subgroup (MulAut V), CFSG.Open.IsComponentOf L' X → L ≠ L' → ⁅L', A⁆ = ⊥ :=
    fun L' hL' hne => commutator_eq_bot_of_natural hV hA hL hW hcV hAcQ hL' hne
  obtain ⟨ρ, hρ⟩ := mStructure_of hmp hO2 hL hA.1.1 hAc π' hπ'i hπ's hLeq'
    (fun V₀ h1 h2 => perm5_normalizer_of_card_four V₀ h1 h2) perm5_stabilizer_coatom
  refine ⟨2, by norm_num, π'.comp (MulAut.conj ρ).toMonoidHom, ?_, symDn_realizesVia_conj hπ'r ρ,
    ?_, ⟨ρ⁻¹ i, ρ⁻¹ j, ?_, ?_⟩, hρ⟩
  · exact hπ's.comp (MulAut.conj ρ).surjective
  · show L = (alternatingGroup (Fin 5)).map
      ((L ⊔ A).subtype.comp (π'.comp (MulAut.conj ρ).toMonoidHom))
    rw [← MonoidHom.comp_assoc, ← Subgroup.map_map, alt_map_conj]
    exact hLeq'
  · exact fun h => hij ((ρ⁻¹).injective h)
  · show A = (Subgroup.zpowers (Equiv.swap (ρ⁻¹ i) (ρ⁻¹ j))).map
      ((L ⊔ A).subtype.comp (π'.comp (MulAut.conj ρ).toMonoidHom))
    have hsw : (MulAut.conj ρ).toMonoidHom (Equiv.swap (ρ⁻¹ i) (ρ⁻¹ j)) = Equiv.swap i j := by
      show ρ * Equiv.swap (ρ⁻¹ i) (ρ⁻¹ j) * ρ⁻¹ = _
      rw [← Equiv.swap_apply_apply]
      simp
    have h : (Subgroup.zpowers (Equiv.swap (ρ⁻¹ i) (ρ⁻¹ j))).map
        ((L ⊔ A).subtype.comp (π'.comp (MulAut.conj ρ).toMonoidHom)) =
        (Subgroup.zpowers (Equiv.swap i j)).map ((L ⊔ A).subtype.comp π') := by
      rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      simp only [MonoidHom.comp_apply, hsw]
    exact hAeq'.trans h.symm

theorem AsB69DeepInputsFour.toRestNoN (h22 : E2.E22StatementNoN)
    (hA21 : AsA21SQTKSection) (h : AsB69DeepInputsFour) : AsB69DeepInputsRest :=
  ⟨h.sp4, h.a6, h.tripleA6, h.g2, asB69AltCase_ofNoN h22 hA21⟩

theorem asB69Component_of_deep_inputs_fourNoN (hB42 : AsB42)
    (hA21 : AsA21SQTKSection) (h22 : E2.E22StatementNoN) (hdeep : AsB69DeepInputsFour) :
    AsB69Component :=
  asB69Component_of_deep_inputs_restNoN hB42 hA21 h22 (hdeep.toRestNoN h22 hA21)

end B69

end Alt

end CFSG.Quasithin
