module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocal
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoUnitaryLocal
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoLocal
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoNbrConj
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem GGSecFiveE6QTwoCfg.orthogonalEnd'
    (hRig : GGLabelRigidInput)
    (hTP : GGNbrTablePNbrInputOnL fun p n labL labJ _ =>
      p = 3 ∧ n = 3 ^ 5 ∧ labL = ⟨.D, 4, 1⟩ ∧ labJ = ⟨.twA, 3, 1⟩)
    (hLB : GGLBalanceInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J)
    (hE6 : GGSecFiveWeylAt 3 B Bs x L D J CoxeterMatrix.E₆)
    (hlab : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = 1)) :
    ∃ (y : G) (K' : Subgroup G), GGNbr 3 B x D J y K' ∧ ⁅L, L⁆ = L ∧ ¬ L ≤ K' ∧
      Bs ≤ L ⊔ K' ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
        (φ : K' ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))),
        USixTwo.LocalSetting hω y K' φ Bs ∧
        ∃ W : Subgroup G, W ≤ Subgroup.normalizer (Bs : Set G) ∧
          W ⊓ Subgroup.centralizer {y} ≤
            (K' ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G) ∧
          (∃ n ∈ W, ∃ hnK : n * y * n⁻¹ ∈ K', φ ⟨n * y * n⁻¹, hnK⟩ = USixTwo.threeA hω) ∧
          ∃ g ∈ W, (∀ z ∈ Bs ⊓ K', g * z * g⁻¹ = z) ∧ g * y * g⁻¹ = y⁻¹ := by
  classical
  obtain ⟨hRest, hG, -, hBs, hxB, hx1, horderx, hLx, hstar, hcyc, hNT⟩ :=
    e6QTwo_config_facts hC
  have hcfg : GGConfig 3 B Bs x L D J := hRest.1
  have hIDall : GGInnerDiagAll 3 B Bs x L D J := hRest.2.2.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hcfg.2.2
  obtain ⟨y, K', hNbr, hWeyl⟩ := hE6
  have hAKr : GGReflGenerated 3 (ggAutomizer K' Bs) := by
    obtain ⟨𝒦, hRoute, -⟩ := hC
    exact hRoute.2.1 y K' hNbr
  have hIDK : GGInnerDiagOn Bs K' := hIDall.2 y K' hNbr
  have hBsNK : Bs ≤ Subgroup.normalizer (K' : Set G) := GGInnerDiagOn.le_normalizer hIDK
  have hyB : y ∈ Bs := hcfg.2.1.1 hNbr.1.2.1
  have hy1 : y ≠ 1 := hNbr.1.2.2.1
  have hK'y : K' ≤ Subgroup.centralizer {y} := hNbr.1.2.2.2.1
  have hSclosed : ∀ lab lab' : LargeEvenLabel, GGLabelIso lab lab' →
      (lab'.tag = .D ∧ lab'.rank = 4 ∧ lab'.n = 1) →
      (lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = 1) := by
    intro lab lab' hiso h'
    rw [E6QTwo.eq_of_ggLabelIso_end hiso ⟨Or.inr (Or.inl ⟨h'.1, h'.2.1⟩), h'.2.2⟩]
    exact h'
  obtain ⟨hperf, K₂, _, _, θ, hK2, hBsN, hI⟩ := exists_omegaPlusDatum_of_innerDiagOnLabel_D4
    (E6QTwo.innerDiagOnLabel_of_marking (p := 3) hRig hSclosed hIDall.1 hlab)
  have hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian Nat.prime_three hBs hxB hx1 hLx
      (fun S hSL hSp => hcyc S hSp hSL)
  have hZ2 : IsPGroup 2 (Subgroup.center L) :=
    E6QTwo.isPGroup_two_center_of_omegaPlus hK2 θ hperf
  have hAind : ∀ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K' Bs, φ ∈ ggInduced ⊤ Bs := by
    intro φ hφ
    obtain ⟨g, -, hgN, hg⟩ := mem_ggAutomizer_iff.mp
      (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ)
    exact ⟨g, Subgroup.mem_top g, hgN, hg⟩
  have hcard : Nat.card Bs = 3 ^ 5 :=
    le_antisymm (E6QTwo.card_le_three_pow_five_of_omegaPlus hK2 θ hperf hBs hBL hBsN hI)
      (E6QTwo.three_pow_five_le_card hBs hNT hAind hWeyl)
  have hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4 :=
    E6QTwo.card_inf_eq_of_omegaPlus hK2 θ hperf hZ2 hBs hcard hx1 hBL hstar hBsN hI
  obtain ⟨hAL192, hALr⟩ := E6QTwo.card_ggAutomizer_eq_of_omegaPlus hK2 θ hZ2 hBs hcard
    hcardE hx1 hLx hBL hstar
  obtain ⟨hDB, -, hDcard, hxD, -, hJ, -⟩ := hDJ.1
  obtain ⟨hlabJ, hJaut, h6⟩ := E6QTwo.hasLabel_and_ggAutomizer_of_omegaPlus hK2 θ hperf hZ2
    hBs hcard hcardE hx1 hLx hBL hstar hBsN hI (hDB.trans hcfg.2.1.1) hDcard hxD hJ
  have hJK : J ≤ K' :=
    le_of_ggNbr hLB hcfg.1 hDJ (E6QTwo.three_dvd_card_of_hasLabel_twA3 hlabJ) hNbr
  have hxy : (⟨y, hyB⟩ : ↥Bs) ∉ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hyx : y ∈ Subgroup.zpowers x :=
      Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hD : D ≤ Subgroup.zpowers x := by
      rw [hNbr.2.1, Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact Subgroup.mem_zpowers z
      · exact hyx
    have h9 := Subgroup.card_le_of_le hD
    rw [hDcard, Nat.card_zpowers, horderx] at h9
    norm_num at h9
  have : Finite (MulAut ↥Bs) :=
    Finite.of_injective (fun f : MulAut ↥Bs => (f : ↥Bs → ↥Bs)) fun f g h =>
      MulEquiv.ext (congrFun h)
  have h6' : 6 ≤ Set.ncard {r : MulAut ↥Bs | r ∈ ggAutomizer L Bs ⊓ ggAutomizer K' Bs ∧
      GGIsReflection 3 r} := by
    refine h6.trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
    rintro r ⟨hrL, hr, hrD⟩
    exact ⟨⟨hrL, ggAutomizer_mono Bs hJK (hJaut r hrL hrD)⟩, hr⟩
  have hK'comp : CFSG.Assembly.IsComponentOf K' (Subgroup.centralizer ({y} : Set G)) :=
    (isComponentOf_of_isNeighborOf hcfg.1.2.2.2.2.2.2.2 (isNeighborOf_of_ggNbr hDJ hNbr)).1
  have hdich : ∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K' Bs, ψ ⟨y, hyB⟩ = ⟨y, hyB⟩ →
      (∀ a ∈ ggAutomizer K' Bs, ψ * a * ψ⁻¹ ∈ ggAutomizer K' Bs) ∨
        ∀ a ∈ ggAutomizer K' Bs, ∀ b ∈ ggAutomizer K' Bs,
          a * (ψ * b * ψ⁻¹) = ψ * b * ψ⁻¹ * a :=
    fun ψ hψ hψy => ggAutomizer_conj_mem_or_commute hyB hK'comp
      (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hψ) hψy
  obtain ⟨hAK9, hfix, hCcard, hyC⟩ := E6QTwo.card_eq_of_weylOfType_E6_of_card_192 hBs hNT
    hcard card_coxeterE6_group hAind hWeyl hAL192 hALr hAKr (fun h => hx1 (congrArg Subtype.val h))
    (fun φ hφ => ggAutomizer_apply_eq_of_le_centralizer (x := ⟨x, hxB⟩) hLx hφ)
    (fun φ hφ => ggAutomizer_apply_eq_of_le_centralizer (x := ⟨y, hyB⟩) hK'y hφ) hxy h6' hdich
  have h36 : 3 ^ 6 ∣ Nat.card (K' ⧸ Subgroup.center K') :=
    E6QTwo.three_pow_six_dvd_card_center_quot hBs hNT hyB hK'y hBsNK hfix hAK9 hCcard hyC
  have hlabK : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1)
      3 Bs K' :=
    E6QTwo.innerDiagOnLabel_twA5_of_nbr hRig hTP hcfg hIDall.1 hIDK hNbr hcard hlab hlabJ h36
  obtain ⟨hperfK, K, hfieldK, hfiniteK, θK, hK4, -, hIK⟩ :=
    exists_unitaryDatum_of_innerDiagOnLabel_twA5 hlabK
  have hcycK : ∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer (K' : Set G) →
      IsCyclic S :=
    E6QTwo.isCyclic_of_le_centralizer_of_nbr hBs hcard hyB hK'y hBsNK hstar hfix hCcard hyC
  have hSK : LargeEvenSStar 3 B y K' :=
    ⟨hNbr.1.1, hNbr.1.2.1, hy1,
      (isComponentOf_of_isNeighborOf hcfg.1.2.2.2.2.2.2.2 (isNeighborOf_of_ggNbr hDJ hNbr)).1,
      fun S hSK hSp => hcycK S hSp hSK⟩
  have hmarkK : LargeEvenMarking K'
      (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hlabK
  have hWeyl' : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizer K' Bs ⊔ ggAutomizer L Bs) := by
    rwa [sup_comm]
  obtain ⟨ω, hω, φ, hLS, hWpkg⟩ := E6QTwo.exists_localSetting_and_package hG hK4 θK hperfK hBs
    hNT hcard hyB hy1 hK'y (E6QTwo.normal_of_sStar_of_marking_twA5 hSK hmarkK) hcycK hstar
    hBsNK hIK hWeyl'
  refine ⟨y, K', hNbr, ?_, E6QTwo.not_le_of_weylOfType_E6 hBs hNT hyB hy1 hK'y hWeyl' hcard,
    E6QTwo.le_sup_of_weylOfType_E6 hBs hNT hBsN hBsNK hWeyl hcard, K, hfieldK, hfiniteK, ω, hω,
    φ, hLS, hWpkg⟩
  rw [← Subgroup.map_subtype_commutator L, hperf, Subgroup.map_top, Subgroup.range_subtype]

end CFSG.StandardType

end
