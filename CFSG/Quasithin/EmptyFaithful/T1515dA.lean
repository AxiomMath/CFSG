module

public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Background.InternalSecIrr
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.EmptyFaithful.T1515cA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.InternalSec
open scoped Pointwise commutatorElement IsMulCommutative

variable {G : Type} [Group G]

theorem conjClosure_sup_eq1527d {L S Z : Subgroup G} (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hSZ : S ≤ Subgroup.centralizer (Z : Set G)) : conjClosure Z (L ⊔ S) = conjClosure Z L := by
  refine le_antisymm (conjClosure_le fun h hh z hz => ?_) (conjClosure_mono le_rfl le_sup_left)
  have hh' : h ∈ (L : Set G) * (S : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L S hSN]
    exact hh
  obtain ⟨l, hl, s, hs, rfl⟩ := hh'
  have hsz : s * z = z * s := (Subgroup.mem_centralizer_iff.mp (hSZ hs) z hz).symm
  have e : l * s * z * (l * s)⁻¹ = l * z * l⁻¹ := by
    calc l * s * z * (l * s)⁻¹ = l * (s * z) * s⁻¹ * l⁻¹ := by group
      _ = l * (z * s) * s⁻¹ * l⁻¹ := by rw [hsz]
      _ = l * z * l⁻¹ := by group
  rw [e]
  exact mem_conjClosure hl hz

theorem le_centralizer_of_le_omegaOneCenter1527d {S Z : Subgroup G}
    (hZ : Z ≤ quasithinOmegaOneCenter S) : S ≤ Subgroup.centralizer (Z : Set G) := by
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzc := (B2F.omegaOneCenter_le_inf_centralizer S (hZ hz)).2
  exact (Subgroup.mem_centralizer_iff.mp hzc s hs).symm

variable [Finite G]

theorem isTwoReducedIn_conjClosure_sup1527d {L S Z : Subgroup G} (hS : IsSylowTwoOf S (L ⊔ S))
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hF : CharTwo L)
    (hZ : Z ≤ quasithinOmegaOneCenter S) :
    IsElemAbelian 2 (conjClosure Z L) ∧ IsTwoReducedIn (L ⊔ S) (conjClosure Z L) := by
  have hSZ := le_centralizer_of_le_omegaOneCenter1527d hZ
  have hF' : CharTwo (L ⊔ S) := charTwo_sup_of_odd_quotient1515c hS.2.1 hSN hF
  obtain ⟨-, hel, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hS hF' hZ
  rw [conjClosure_sup_eq1527d hSN hSZ] at hel hred
  exact ⟨hel, hred⟩

section AutOn

variable {L Y U : Subgroup G}

omit [Finite G] in
theorem pCoreOf_autOn_L_eq_bot1527d (hLY : L ≤ Y) (hYL : Y ≤ Subgroup.normalizer (L : Set G))
    (hO2 : pCoreOf 2 (autOn Y U) = ⊥) : pCoreOf 2 (autOn L U) = ⊥ := by
  have hn : ((autOn L U).subgroupOf (autOn Y U)).Normal := by
    refine ⟨fun k hk x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact autOn_normal_of hYL _ x.2 _ hk
  have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _
    (autOn_le_autOn_of_le hLY) hn
  rw [hO2] at this
  exact le_bot_iff.1 this

end AutOn

theorem not_commute_of_isQuasisimple1527d {Ω : Type} [Group Ω] {K : Subgroup Ω}
    (hK : CFSG.IsQuasisimple ↥K) (h : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) : False := by
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_isQuasisimple hK
  exact hab (Subtype.ext (h a a.2 b b.2))

theorem commutator_eq_or_eq_bot1527d {Ω : Type*} [Group Ω] {K A : Subgroup Ω}
    (hK : CFSG.IsQuasisimple ↥K) (hA : A ≤ Subgroup.normalizer (K : Set Ω)) :
    ⁅K, A⁆ = K ∨ ⁅K, A⁆ = ⊥ := by
  have hle : ⁅K, A⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hA
  have hN : ((⁅K, A⁆ : Subgroup Ω).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      (Subgroup.normalizer_commutator_ge_left K A)
  have hKo := B1Red.isQuasisimple_to_open hK
  have hKK : ⁅K, K⁆ = K := by
    have h2 := Subgroup.map_commutator (⊤ : Subgroup ↥K) ⊤ K.subtype
    rw [← commutator_def, hKo.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    exact h2.symm
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hKo
      ((⁅K, A⁆ : Subgroup Ω).subgroupOf K) with h | h
  · right
    have hc : ⁅⁅K, A⁆, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hx' : (⟨x, hle hx⟩ : ↥K) ∈ (⁅K, A⁆ : Subgroup Ω).subgroupOf K := hx
      have := Subgroup.mem_center_iff.mp (h hx') ⟨k, hk⟩
      exact congrArg Subtype.val this
    have hc' : ⁅⁅A, K⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm A K]; exact hc
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate hc hc'
    rwa [hKK] at h3
  · left
    refine le_antisymm hle fun k hk => ?_
    have : (⟨k, hk⟩ : ↥K) ∈ (⁅K, A⁆ : Subgroup Ω).subgroupOf K := by rw [h]; trivial
    exact this

section Offender

variable {S L Y W : Subgroup G} [IsMulCommutative ↥W]

omit [Finite G] [IsMulCommutative ↥W] in
theorem conjAct_mem_autOn1527d (hLW : L ≤ Subgroup.normalizer (W : Set G)) {l : G} (hl : l ∈ L) :
    conjAct W ⟨l, hLW hl⟩ ∈ autOn L W :=
  Setup.mem_autOn_iff.2 ⟨⟨l, hLW hl⟩, hl, rfl⟩

theorem exists_offender1527d (hWe : IsElemAbelian 2 W) (hred : IsTwoReducedIn Y W)
    (hSY : IsSylowTwoOf S Y) (hLY : L ≤ Y) (hYL : Y ≤ Subgroup.normalizer (L : Set G))
    (hq : CFSG.IsQuasisimple ↥(autOn L W)) (hJ : L = ⁅L, thompsonJ S⁆)
    (hLW : ¬ L ≤ Subgroup.centralizer (W : Set G)) :
    ∃ A : Subgroup G, IsMaxElemAbelian S A ∧
      IsFFStarOffender (autOn Y W) (autOn A W) ∧ ⁅autOn L W, autOn A W⁆ = autOn L W := by
  have hTN : S ≤ Subgroup.normalizer (L : Set G) := hSY.1.trans hYL
  have hTW : S ≤ Subgroup.normalizer (W : Set G) := hSY.1.trans hred.2.1
  have hLN : L ≤ Subgroup.normalizer (W : Set G) := hLY.trans hred.2.1
  have hnorm : ∀ A : Subgroup G, A ≤ S →
      autOn A W ≤ Subgroup.normalizer (autOn L W : Set (MulAut ↥W)) := by
    intro A hAT x hx
    have hc := autOn_normal_of (U := W) (hAT.trans hTN)
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hc x hx k hk, fun hk => ?_⟩
    have := hc x⁻¹ ((autOn A W).inv_mem hx) _ hk
    simpa [mul_assoc] using this
  by_cases hex : ∃ A : Subgroup G, IsMaxElemAbelian S A ∧ ⁅autOn L W, autOn A W⁆ = autOn L W
  · obtain ⟨A, hA, hLA⟩ := hex
    have hAC : ¬ A ≤ Subgroup.centralizer (W : Set G) := by
      intro hAC
      have h0 : autOn A W = ⊥ := autI_eq_bot_of_le_centralizer hWe hAC
      rw [h0, Subgroup.commutator_bot_right] at hLA
      refine not_commute_of_isQuasisimple1527d hq fun a ha b hb => ?_
      rw [← hLA, Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    have hoff : IsFFOffender Y W A := ⟨isMaxElemAbelian_of_isSylowTwoOf hSY hA, hAC⟩
    exact ⟨A, hA, offenderImages_isFFStarOffender hWe hred.1 hred.2.1 ⟨A, hoff, rfl⟩, hLA⟩
  · exfalso
    push Not at hex
    have hbot : ∀ A : Subgroup G, IsMaxElemAbelian S A →
        autOn A W ≤ Subgroup.centralizer (autOn L W : Set (MulAut ↥W)) := by
      intro A hA
      rcases commutator_eq_or_eq_bot1527d hq (hnorm A hA.1) with h1 | h1
      · exact absurd h1 (hex A hA)
      · rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact (Subgroup.mem_centralizer_iff.mp (h1 hk) x hx).symm
    set S' : Subgroup G :=
      ((Subgroup.centralizer (autOn L W : Set (MulAut ↥W))).comap (conjAct W)).map
        (Subgroup.normalizer (W : Set G)).subtype with hS'
    have hJS : thompsonJ S ≤ S' := by
      refine iSup₂_le fun A hA => ?_
      intro a ha
      have haN : a ∈ Subgroup.normalizer (W : Set G) := hTW (hA.1 ha)
      exact ⟨⟨a, haN⟩, hbot A hA (Setup.mem_autOn_iff.2 ⟨⟨a, haN⟩, ha, rfl⟩), rfl⟩
    apply hLW
    rw [hJ, Subgroup.commutator_le]
    intro l hl j hj
    obtain ⟨g, hg, rfl⟩ := hJS hj
    set lN : ↥(Subgroup.normalizer (W : Set G)) := ⟨l, hLN hl⟩
    have hlK : conjAct W lN ∈ autOn L W := conjAct_mem_autOn1527d hLN hl
    have hcomm : conjAct W ⁅lN, g⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp hg _ hlK)
    exact (convI_eq_one_iff hWe ⁅lN, g⁆).1 hcomm

end Offender

section B51

variable {S L Y U : Subgroup G} [IsMulCommutative ↥U]

theorem b51Hyp_1527d (hS : IsSylowTwoOf S Y) (hLY : L ≤ Y) (hYL : Y ≤ Subgroup.normalizer (L : Set G))
    (hY2 : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ L) (hUe : IsElemAbelian 2 U) (hred : IsTwoReducedIn Y U)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hSQ : SQTKGroup ↥L) (hLU : ¬ L ≤ Subgroup.centralizer (U : Set G))
    (hJ : L = ⁅L, thompsonJ S⁆) :
    B51Hyp (ffJ (autOn Y U)) (autOn L U) := by
  have hLN : L ≤ Subgroup.normalizer (U : Set G) := hLY.trans hred.2.1
  have hO2 : pCoreOf 2 (autOn Y U) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hO2L : pCoreOf 2 (autOn L U) = ⊥ := pCoreOf_autOn_L_eq_bot1527d hLY hYL hO2
  have hqa : CFSG.IsQuasisimple ↥(autOn L U) := isQuasisimple_autOn hLN hq hO2L hLU
  have hker : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (U : Set G)) :=
    isPGroup_ker_of_simple hLN hsimple hO2L hLU
  have hSQa : SQTKGroup ↥(autOn L U) := sqtkGroup_autOn hLN hSQ hker
  have h2 : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ L ⊔ Subgroup.centralizer (U : Set G) := fun y hy => by
    obtain ⟨e, he⟩ := hY2 y hy
    exact ⟨e, Subgroup.mem_sup_left he⟩
  obtain ⟨A, -, hA, hLA⟩ := exists_offender1527d hUe hred hS hLY hYL hqa hJ hLU
  exact (b51Hyp_ffJ_autOn hred.2.1 hLY hYL h2 hO2 hqa hSQa hA hLA).1

end B51

end CFSG.Quasithin
