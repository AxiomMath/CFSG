module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarDelta
public import CFSG.Goldschmidt75.Sec45b
public import CFSG.GH74.Uniqueness.Section15Bender
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallU4Nat
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.HardMathSupport.U4FF (NaturalSU4 NaturalOmega6 disp)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.GH74.Uniqueness.Section15Bender
open scoped commutatorElement Pointwise Matrix

theorem exists_conj_le_of_isElemAbelian2 {U : Type} [CommGroup U] [Finite U]
    {S G A : Subgroup (MulAut U)} (hcyc : IsCyclic (Outer ↥S)) (hSG : S ≤ G)
    (hGN : G ≤ Subgroup.normalizer (S : Set (MulAut U))) (hidx : S.relIndex G = 2)
    (hCodd : Odd (Nat.card (Subgroup.centralizer (S : Set (MulAut U)))))
    (hAN : A ≤ Subgroup.normalizer (S : Set (MulAut U))) (hA : IsElemAbelian2 A) :
    ∃ g ∈ Subgroup.normalizer (S : Set (MulAut U)), conjAutSub g A ≤ G := by
  classical
  have : IsCyclic (Outer ↥S) := hcyc
  let C : Subgroup (MulAut U) := Subgroup.centralizer (S : Set (MulAut U))
  have hC_le_N : C ≤ Subgroup.normalizer (S : Set (MulAut U)) :=
    Subgroup.centralizer_le_normalizer _
  have hG_le_NC : G ≤ Subgroup.normalizer (C : Set (MulAut U)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hc s hs
      have hgN : g ∈ Subgroup.normalizer (S : Set (MulAut U)) := hGN hg
      have hg'inv : g⁻¹ ∈ Subgroup.normalizer (S : Set (MulAut U)) :=
        (Subgroup.normalizer (S : Set (MulAut U))).inv_mem hgN
      have hs'' : g⁻¹ * s * g ∈ S := (Subgroup.mem_normalizer_iff.mp hg'inv s).mp hs
      have hcomm : c * (g⁻¹ * s * g) = (g⁻¹ * s * g) * c := (hc (g⁻¹ * s * g) hs'').symm
      calc
        s * (g * c * g⁻¹) = g * (g⁻¹ * s * g) * c * g⁻¹ := by group
        _ = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [hcomm]
        _ = (g * c * g⁻¹) * s := by group
    · intro hc s hs
      have hgN : g ∈ Subgroup.normalizer (S : Set (MulAut U)) := hGN hg
      have hs' : g * s * g⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hgN s).mp hs
      have hcomm : (g * s * g⁻¹) * (g * c * g⁻¹) = (g * c * g⁻¹) * (g * s * g⁻¹) :=
        hc (g * s * g⁻¹) hs'
      calc
        s * c = g⁻¹ * (g * s * g⁻¹) * (g * c * g⁻¹) * g := by group
        _ = g⁻¹ * ((g * s * g⁻¹) * (g * c * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * c * g⁻¹) * (g * s * g⁻¹)) * g := by rw [hcomm]
        _ = c * s := by group
  let φG : G →* Outer ↥S := (outerHom S).comp (Subgroup.inclusion hGN)
  let φA : A →* Outer ↥S := (outerHom S).comp (Subgroup.inclusion hAN)
  let S' : Subgroup G := S.subgroupOf G
  have hS_ker : S' ≤ φG.ker := by
    intro s hs
    rw [MonoidHom.mem_ker]
    exact (outerHom_eq_one_iff (L := S) (Subgroup.inclusion hGN s)).mpr
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hs))
  have hOutG_card : Nat.card φG.range = 2 := by
    have hcard : Nat.card φG.ker * Nat.card φG.range = Nat.card G := by
      rw [← Subgroup.index_ker φG]
      exact Subgroup.card_mul_index φG.ker
    have hGcard : Nat.card G = Nat.card S * 2 := by
      rw [CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex hSG, hidx]
    rw [hGcard] at hcard
    have hker_ne_top : φG.ker ≠ ⊤ := by
      intro hker_top
      have htriv : ∀ g : G, φG g = 1 := by
        intro g
        have : g ∈ φG.ker := by rw [hker_top]; exact Subgroup.mem_top g
        rwa [MonoidHom.mem_ker] at this
      have hGS : G ≠ S := by
        intro h
        rw [h, S.relIndex_self] at hidx
        omega
      have hex : ∃ g : G, (g : MulAut U) ∉ S := by
        by_contra h
        push Not at h
        have hG_le_S : G ≤ S := fun g hg => h ⟨g, hg⟩
        exact hGS (le_antisymm hG_le_S hSG)
      obtain ⟨g, hgS⟩ := hex
      have hne : φG g ≠ 1 := by
        intro h
        have hg_sup : (g : MulAut U) ∈ S ⊔ C := by
          simpa only [C, Subgroup.coe_inclusion] using
            (outerHom_eq_one_iff (L := S) (Subgroup.inclusion hGN g)).mp h
        obtain ⟨s, hs, c, hc, hgc⟩ := CFSG.GH74.Uniqueness.Bender.exists_mul_of_mem_sup_of_commute
          (fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha) hg_sup
        have hx_eq : s⁻¹ * (g : MulAut U) = c := by rw [hgc]; group
        have hcG : s⁻¹ * (g : MulAut U) ∈ G := G.mul_mem (G.inv_mem (hSG hs)) g.2
        have hcC : s⁻¹ * (g : MulAut U) ∈ C := by rw [hx_eq]; exact hc
        have hcS : s⁻¹ * (g : MulAut U) ∉ S := by
          intro hcS
          apply hgS
          have : (g : MulAut U) = s * (s⁻¹ * (g : MulAut U)) := by group
          rw [this]
          exact S.mul_mem hs hcS
        have hc2S : (s⁻¹ * (g : MulAut U)) ^ 2 ∈ S := by
          have hcG' : s⁻¹ * (g : MulAut U) ∈ G := hcG
          have hS'idx : S'.relIndex ⊤ = 2 := by
            have := Subgroup.relIndex_subgroupOf (H := S) (K := G) (L := G) (hKL := le_rfl)
            simpa [S', Subgroup.subgroupOf_self] using this.trans hidx
          have hidx' : (S.subgroupOf G).index = 2 := by
            simpa [S', Subgroup.relIndex_top_right] using hS'idx
          have : (S.subgroupOf G).Normal :=
            Subgroup.normal_subgroupOf_of_le_normalizer (H := G) (N := S) hGN
          have hmem : (s⁻¹ * (g : MulAut U)) ^ 2 ∈ S := by
            have hmem' := (S.subgroupOf G).sq_mem_of_index_two hidx'
              ⟨s⁻¹ * (g : MulAut U), hcG'⟩
            simpa [Subgroup.mem_subgroupOf] using hmem'
          exact hmem
        have hc_odd : Odd (orderOf (s⁻¹ * (g : MulAut U))) := by
          have hdvd : orderOf (s⁻¹ * (g : MulAut U)) ∣ Nat.card C := by
            exact Subgroup.orderOf_dvd_natCard C hcC
          exact hCodd.of_dvd_nat hdvd
        have hc_in_S : s⁻¹ * (g : MulAut U) ∈ S :=
          CFSG.Goldschmidt75.mem_of_sq_mem_of_odd hc_odd hc2S
        exact hcS hc_in_S
      exact hne (htriv g)
    have hker_eq_S : φG.ker = S' := by
      have hle : φG.ker ≤ S' := by
        by_contra hle_not
        have hlt : S' < φG.ker := lt_of_le_of_ne hS_ker (by
          intro h
          apply hle_not
          rw [h])
        have hltG : φG.ker < ⊤ := lt_of_le_of_ne le_top (by
          intro h
          exact hker_ne_top h)
        have hrel : S'.relIndex ⊤ = S'.relIndex φG.ker * φG.ker.relIndex ⊤ := by
          rw [Subgroup.relIndex_mul_relIndex S' φG.ker ⊤ hlt.le hltG.le]
        have hS'idx : S'.relIndex ⊤ = 2 := by
          have this : S'.relIndex ⊤ = S.relIndex G := by
            simpa [S', Subgroup.subgroupOf_self] using
              (Subgroup.relIndex_subgroupOf (H := S) (K := G) (L := G) (hKL := le_rfl))
          exact this.trans hidx
        rw [hS'idx] at hrel
        have h1 : 2 ≤ S'.relIndex φG.ker := by
          by_contra h
          have : S'.IsFiniteRelIndex φG.ker :=
            Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance
          have hpos : 0 < S'.relIndex φG.ker := Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
          have h1 : S'.relIndex φG.ker = 1 := by omega
          rw [Subgroup.relIndex_eq_one] at h1
          exact (lt_iff_le_not_ge.mp hlt).2 h1
        have h2 : 2 ≤ φG.ker.relIndex ⊤ := by
          by_contra h
          have : φG.ker.IsFiniteRelIndex ⊤ :=
            Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance
          have hpos : 0 < φG.ker.relIndex ⊤ := Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
          have h2 : φG.ker.relIndex ⊤ = 1 := by omega
          rw [Subgroup.relIndex_eq_one] at h2
          exact (lt_iff_le_not_ge.mp hltG).2 h2
        have : 4 ≤ S'.relIndex ⊤ := by
          calc
            4 = 2 * 2 := by norm_num
            _ ≤ S'.relIndex φG.ker * φG.ker.relIndex ⊤ := Nat.mul_le_mul h1 h2
            _ = S'.relIndex ⊤ := hrel.symm.trans hS'idx.symm
        omega
      exact le_antisymm hle hS_ker
    rw [hker_eq_S] at hcard
    have hS'card : Nat.card S' = Nat.card S := by
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSG).toEquiv
    rw [hS'card] at hcard
    have hSpos : 0 < Nat.card S := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hSpos hcard
  have hA_map_le : φA.range ≤ φG.range := by
    rw [IsCyclic.subgroup_le_iff_card_dvd]
    rw [hOutG_card]
    have hexp : ∀ x ∈ φA.range, x ^ 2 = 1 := by
      rintro _ ⟨a, rfl⟩
      have h_a_sq : a ^ 2 = 1 := by
        apply Subtype.ext
        simpa using hA.2 (a : MulAut U) a.2
      rw [← map_pow, h_a_sq, map_one]
    have hdvd : Nat.card φA.range ∣ 2 := by
      have hH_cyc : IsCyclic ↥φA.range := by
        have : IsCyclic ↥(⊤ : Subgroup (Outer ↥S)) :=
          (MulEquiv.isCyclic Subgroup.topEquiv).mpr hcyc
        exact isCyclic_of_injective (Subgroup.inclusion le_top)
          (Subgroup.inclusion_injective le_top)
      obtain ⟨g, hg_gen⟩ := IsCyclic.exists_generator (α := ↥φA.range)
      have hg_sq : g ^ 2 = 1 := by
        have : (g : Outer ↥S) ^ 2 = 1 := hexp g g.2
        exact Subtype.ext (by simpa using this)
      have hg_dvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg_sq
      rw [← orderOf_eq_card_of_forall_mem_zpowers hg_gen]
      exact hg_dvd
    exact hdvd
  have hA_le_GC : A ≤ G ⊔ C := by
    intro a ha
    have hmem : φA ⟨a, ha⟩ ∈ φG.range := by
      have hle := SetLike.le_def.mp hA_map_le
      exact hle ⟨⟨a, ha⟩, rfl⟩
    rw [MonoidHom.mem_range] at hmem
    obtain ⟨g, hg_eq⟩ := hmem
    have h_eq : φA ⟨a, ha⟩ * (φG g)⁻¹ = 1 := by
      rw [hg_eq, mul_inv_cancel]
    have h_eq2 :
        outerHom S (Subgroup.inclusion hAN ⟨a, ha⟩ * (Subgroup.inclusion hGN g)⁻¹) = 1 := by
      rw [map_mul, map_inv]
      simpa only [φA, φG, MonoidHom.comp_apply] using h_eq
    have hmem : a * (g : MulAut U)⁻¹ ∈ S ⊔ C := by
      simpa only [C, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion] using
        (outerHom_eq_one_iff (L := S) _).mp h_eq2
    have hmemGC : a * (g : MulAut U)⁻¹ ∈ G ⊔ C :=
      (sup_le (hSG.trans le_sup_left) le_sup_right) hmem
    have hgGC : (g : MulAut U) ∈ G ⊔ C := Subgroup.mem_sup_left g.2
    have ha_eq : a = (a * (g : MulAut U)⁻¹) * (g : MulAut U) := by group
    rw [ha_eq]
    exact Subgroup.mul_mem (G ⊔ C) hmemGC hgGC
  obtain ⟨P, hP⟩ := CFSG.Quasithin.E1.exists_isSylowIn_two G
  have hP_GC : IsSylowIn 2 P (G ⊔ C) := by
    refine ⟨?_, ?_, ?_⟩
    · exact hP.le.trans le_sup_left
    · exact hP.isPGroup
    · have hrel : P.relIndex (G ⊔ C) = P.relIndex G * G.relIndex (G ⊔ C) := by
        rw [Subgroup.relIndex_mul_relIndex P G (G ⊔ C) hP.le le_sup_left]
      rw [hrel]
      have hodd1 : Odd (P.relIndex G) := by
        have := hP.not_dvd_relIndex
        exact Nat.not_even_iff_odd.mp (by
          intro heven
          exact this (even_iff_two_dvd.mp heven))
      have hodd2 : Odd (G.relIndex (G ⊔ C)) := by
        have h_eq : G.relIndex (G ⊔ C) = (G ⊓ C).relIndex C :=
          (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hG_le_NC).1
        rw [h_eq]
        have hdvd : (G ⊓ C).relIndex C ∣ Nat.card C := Subgroup.relIndex_dvd_card _ _
        exact hCodd.of_dvd_nat hdvd
      rw [← even_iff_two_dvd]
      exact Nat.not_even_iff_odd.mpr (Odd.mul hodd1 hodd2)
  obtain ⟨g, hgGC, hgA⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.exists_conj_le_of_quasithin_isSylowIn
      hP_GC hA_le_GC (CFSG.Quasithin.E3.isPGroup_of_isElemAbelian2 hA)
  have hgN : g ∈ Subgroup.normalizer (S : Set (MulAut U)) := by
    have hGC_le_N : G ⊔ C ≤ Subgroup.normalizer (S : Set (MulAut U)) := sup_le hGN hC_le_N
    exact hGC_le_N hgGC
  refine ⟨g, hgN, ?_⟩
  exact hgA.trans hP.le

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
