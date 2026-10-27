module

public import CFSG.Quasithin.Vol2.Ch11SecU1U3Q
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IH
public import CFSG.Quasithin.Vol2.Ch11SecU1Mem1
public import CFSG.Quasithin.Vol2.Ch11SecU1Mem3
public import CFSG.Quasithin.Vol2.Ch11SecU1U3H
public import CFSG.Quasithin.Vol2.Ch11SecU1U3N

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.U3

open CFSG.Quasithin.E2P.Asc80 CFSG.Quasithin CFSG.Open CFSG.Quasithin.E1
open CFSG.Quasithin.A312U3 (uniData)
open scoped MatrixGroups

section Model

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]

theorem eq_one_or_eq_zcU_of_mem_centralizer_leviSL (hp5 : p = 5) (hF : Nat.card F = p ^ 2)
    {c : PSU3F p F} (hc : c ∈ Subgroup.centralizer (leviSL hF : Set (PSU3F p F))) :
    c = 1 ∨ c = zcU hF := by
  subst hp5
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hcB : c ∈ leviCU hF := mem_leviCU_of_commute_z hp2 hF
    (Subgroup.mem_centralizer_iff.mp hc _ (zcU_mem_leviSL hF)).symm
  obtain ⟨_, ⟨N, rfl⟩, rfl⟩ := hcB
  obtain ⟨μ, hμ⟩ := scalar_of_piU_mem_centralizer_leviSL hp2 hF hc
  exact piU_blkU_scalar hF hμ (pow_succ_eq_one_of_scalar hF hμ)

variable {G : Type} [Group G] {L : Subgroup G}

theorem exists_levi_data_five (hp5 : p = 5) (hF : Nat.card F = p ^ 2) (hLn : L.Normal)
    (ψ : PSU3F p F ≃* ↥L) {y : G} (hyL : y ∈ L) (hy2 : orderOf y = 2) :
    ∃ Y : Subgroup G, Y ≤ L ∧ Y ≤ Subgroup.centralizer ({y} : Set G) ∧
      Subgroup.centralizer ({y} : Set G) ≤ Subgroup.normalizer (Y : Set G) ∧
      Nonempty (↥Y ≃* SL(2, ZMod p)) ∧ y ∈ Y ∧
      ∀ g ∈ L, g ∈ Subgroup.centralizer (Y : Set G) → g = 1 ∨ g = y := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨ψ', hψ'⟩ := exists_equiv_zcU hp2 hF ψ hyL hy2
  set f := embU ψ' with hf
  have hfinj : Function.Injective f := embU_injective ψ'
  have hCL : L ⊓ Subgroup.centralizer ({y} : Set G) = (leviCU hF).map f := by
    rw [← hψ', inf_centralizer_embU, centralizer_zcU hp2 hF]
  set Y : Subgroup G := (leviSL hF).map f with hY
  have hYcomm : Y = ⁅L ⊓ Subgroup.centralizer ({y} : Set G),
      L ⊓ Subgroup.centralizer ({y} : Set G)⁆ := by
    rw [hCL, ← Subgroup.map_commutator, commutator_leviCU (by omega) hF]
  have hYC0 : Y ≤ L ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hCL]
    exact Subgroup.map_mono (leviSL_le_leviCU hF)
  have hCY : L ⊓ Subgroup.centralizer (Y : Set G) =
      (Subgroup.centralizer (leviSL hF : Set (PSU3F p F))).map f :=
    inf_centralizer_map_embU ψ' (leviSL hF)
  refine ⟨Y, hYC0.trans inf_le_left, hYC0.trans inf_le_right, ?_,
    ⟨((leviSL hF).equivMapOfInjective f hfinj).symm.trans (leviSLEquiv hF).symm⟩,
    ⟨zcU hF, zcU_mem_leviSL hF, hψ'⟩, fun g hgL hgC => ?_⟩
  · rw [hYcomm]
    exact CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer _ _ _
      (centralizer_le_normalizer_inf hLn y) (centralizer_le_normalizer_inf hLn y)
  · have hg : g ∈ (Subgroup.centralizer (leviSL hF : Set (PSU3F p F))).map f := by
      rw [← hCY]
      exact ⟨hgL, hgC⟩
    obtain ⟨c, hc, rfl⟩ := hg
    rcases eq_one_or_eq_zcU_of_mem_centralizer_leviSL hp5 hF hc with rfl | rfl
    · exact Or.inl (map_one f)
    · exact Or.inr hψ'

variable [Finite G]

theorem inner_nParam_five (hp5 : p = 5) (hF : Nat.card F = p ^ 2)
    (hAS : SecE3.AlmostSimple L) (ψ : PSU3F p F ≃* ↥L) :
    ∀ x ∈ L, orderOf x = 2 → nParam (Subgroup.centralizer ({x} : Set G)) ≤ 1 := by
  intro x hxL hx2
  have hLn := hAS.normal
  obtain ⟨Y, hYL, hYC, hYn, ⟨e⟩, hyY, hLC⟩ := exists_levi_data_five hp5 hF hLn ψ hxL hx2
  obtain ⟨ψh⟩ := exists_hyp_equiv hF ψ
  have hp2 : p ≠ 2 := by omega
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx2
  have hxx : x * x = 1 := by rw [← sq, ← hx2, pow_orderOf_eq_one]
  subst hp5
  exact nParam_centralizer_le_one_five hYL hYC hYn e hyY hx1 hxx hLC hAS.two
    fun t₁ t₂ h1 h2 ho1 ho2 hc =>
      outer_pair (uniData hF) hp2 hAS.centralizer_eq ψh h1 h2 ho1 ho2 hc

end Model


variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

theorem settingL3_psu3_five (hU : IsPSU 3 5 1 ↥(CFSG.generalizedFitting G))
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    L3I.SettingL3 (CFSG.generalizedFitting G) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨F, _, _, hF, ψ, hAS, h2⟩ := exists_psu3_model (by norm_num) hU hs hT hFT
  have := hAS.normal
  have hC := hAS.centralizer_eq
  obtain ⟨ψh⟩ := exists_hyp_equiv hF ψ
  exact
    { almostSimple := hAS
      two_dvd := h2
      inner_conj := inner_conj (by norm_num) hF ψ
      inner_max := fun x hxL hx2 => isCoatom_centralizer (by norm_num) (by norm_num) hF hAS
        (E1.isSylowIn_top_of_quasithinIsSylowTwo hT) ψ hxL hx2
      inner_nParam := inner_nParam_five rfl hF hAS ψ
      inner_torus := inner_torus le_rfl (by norm_num) hF hAS.normal ψ
      outer := outer_sigma le_rfl hF hC ψ
      outer_pair := fun _ _ h1L h2L h1 h2 hc =>
        outer_pair (uniData hF) (by norm_num) hC ψh h1L h2L h1 h2 hc }

theorem nParam_le_one_of_psu3_five (hU : IsPSU 3 5 1 ↥(CFSG.generalizedFitting G))
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 :=
  L3I.nParam_le_one_of_settingL3 torusMember_holds componentMember_holds
    (settingL3_psu3_five hU hs hT hFT)

end CFSG.Quasithin.Vol2.Ch11.SecU1.U3
