module

public import CFSG.Quasithin.Vol2.Ch9KGFFQ
public import CFSG.Quasithin.Vol2.Ch9Sec3FFBCmp

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem autOn_facts' (h56 : AsB56) {Y T K KY U : Subgroup G} [IsMulCommutative ↥U]
    (hSQ : SQTKGroup ↥Y) (hT : IsSylowTwoOf T Y) (hKKY : K ≤ KY) (hKYc : KY ∈ cComp Y)
    (hYKY : Y ≤ Subgroup.normalizer (KY : Set G)) (hred : IsTwoReducedIn Y U)
    (hperf : ⁅K, K⁆ = K) (hA5 : Nonempty (O2Q K ≃* alternatingGroup (Fin 5)))
    (hJ : ¬ ⁅KY, thompsonJ T⁆ ≤ Subgroup.centralizer (U : Set G))
    (hKU : ¬ K ≤ Subgroup.centralizer (U : Set G)) (hq : CFSG.IsQuasisimple (O2Q KY)) :
    CFSG.IsQuasisimple ↥(autOn KY U) ∧ B56QuasisimpleList ↥(autOn KY U) ∧
      60 ∣ Nat.card ↥(autOn KY U) ∧
      ∃ π : O2Q KY →* ↥(autOn KY U), Function.Surjective π := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVe : IsElemAbelian 2 U := hred.2.2.1
  have hYV : Y ≤ Subgroup.normalizer (U : Set G) := hred.2.1
  have hKYY : KY ≤ Y := le_of_mem_cComp hKYc
  have hKYN : KY ≤ Subgroup.normalizer (U : Set G) := hKYY.trans hYV
  have hKN : K ≤ Subgroup.normalizer (U : Set G) := hKKY.trans hKYN
  have hO2 : pCoreOf 2 (autOn Y U) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hle : autOn KY U ≤ autOn Y U := InternalSec.autOn_le_autOn_of_le hKYY
  have hn : ((autOn KY U).subgroupOf (autOn Y U)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hle).mpr fun k a hk ha => ?_
    exact InternalSec.autOn_normal_of (U := U) hYKY a ha k hk
  have hO2KY : pCoreOf 2 (autOn KY U) = ⊥ := by
    have h := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _ hle hn
    rw [hO2] at h
    exact le_bot_iff.1 h
  have hnt : ¬ KY ≤ Subgroup.centralizer (U : Set G) := fun h => hKU (hKKY.trans h)
  have hqA : CFSG.IsQuasisimple ↥(autOn KY U) :=
    InternalSec.isQuasisimple_autOn hKYN hq hO2KY hnt
  obtain ⟨A, -, hA, hLA⟩ := FFD.exists_offender_of_commutator hVe hred hT hKYY hYKY hqA le_rfl hJ
  have hV2 : ∀ w ∈ U, w ^ 2 = 1 := fun w hw => by simpa [pow_two] using hVe.2 w hw
  obtain ⟨hKJ, -, -, -, hcases⟩ :=
    InternalSec.b56Cases_ffJ_autOn h56 hV2 hYV hKYY hYKY hSQ hO2 hA hLA
  have hsnX : IsSubnormal (autOn KY U) (autOn Y U) :=
    A3.subnormal_map (conjAct U)
      (A3.subnormal_comap (Subgroup.normalizer (U : Set G)).subtype (subnormal_of_mem_cComp hKYc))
  have hlist := SBc3.b56QL_of_subnormal hKJ (A3.subnormal_of_le_of_le hsnX hKJ (B6.ffJ_le _))
    hqA hcases
  have h60 : 60 ∣ Nat.card ↥(autOn KY U) :=
    (FFD.card_autOn_dvd hKN hperf hA5 hKU).trans
      (Subgroup.card_dvd_of_le (InternalSec.autOn_le_autOn_of_le hKKY))
  exact ⟨hqA, hlist, h60, QuotientGroup.lift (CFSG.pCore 2 ↥KY) (InternalSec.autOnHom hKYN)
    (InternalSec.pCore_le_ker_autOnHom hKYN hO2KY),
    QuotientGroup.lift_surjective_of_surjective _ _ (InternalSec.autOnHom_surjective hKYN) _⟩

theorem kyStar_cases
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts) (h56 : AsB56)
    {Y T K KY U : Subgroup G} (hSQ : SQTKGroup ↥Y) (hT : IsSylowTwoOf T Y) (hKY : K ≤ Y)
    (hKl : K ∈ lFamily T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hA5 : Nonempty (O2Q K ≃* alternatingGroup (Fin 5))) (hKYc : KY ∈ cComp Y) (hlt : K < KY)
    (hYKY : Y ≤ Subgroup.normalizer (KY : Set G)) (hred : IsTwoReducedIn Y U)
    (hJ : ¬ ⁅KY, thompsonJ T⁆ ≤ Subgroup.centralizer (U : Set G))
    (hnK : ¬ KY ≤ K ⊔ (KY ⊓ Subgroup.centralizer (U : Set G)))
    (hKU : ¬ K ≤ Subgroup.centralizer (U : Set G)) :
    CFSG.IsQuasisimple (O2Q KY) ∧ CFSG.IsQuasisimple ↥(autOn KY U) ∧
      B56QuasisimpleList ↥(autOn KY U) ∧ 60 ∣ Nat.card ↥(autOn KY U) ∧
      (∃ π : O2Q KY →* ↥(autOn KY U), Function.Surjective π) ∧
      (IsSL3 4 (O2Q KY) ∨ IsPSp4 2 2 (O2Q KY) ∨ IsG2 2 2 (O2Q KY) ∨
        IsAlt 7 ↥(autOn KY U)) := by
  have : IsMulCommutative ↥U := hred.2.2.1.1
  have hqbar := isQuasisimple_modO2Image h36 h312 h314 h56 hSQ hT hKY hKl hTK hA5 hKYc hlt hYKY
    hred hJ hnK hKU
  obtain ⟨hlt', h314bar⟩ := FFB.a314_bar h36 h312 h314 hSQ hT hKY hKl hTK hA5 hKYc hlt
  obtain ⟨e⟩ := FFB.nonempty_o2q_equiv hSQ hKYc hYKY
  have hqKY : CFSG.IsQuasisimple (O2Q KY) := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hqbar
  obtain ⟨hqA, hlist, h60, π, hπ⟩ := autOn_facts' h56 hSQ hT hlt.le hKYc hYKY hred
    (perfect_of_mem_cComp hKl) hA5 hJ hKU hqKY
  obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hqKY
  set π' : ↥(modO2Image Y KY) →* ↥(autOn KY U) := π.comp e.symm.toMonoidHom with hπ'
  have hπ's : Function.Surjective π' := hπ.comp e.symm.surjective
  have hne : π'.ker ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := InternalSec.exists_noncomm_of_isQuasisimple hqA
    obtain ⟨x, rfl⟩ := hπ's a
    obtain ⟨y, rfl⟩ := hπ's b
    have hx : x ∈ π'.ker := by rw [htop]; exact Subgroup.mem_top x
    have hy : y ∈ π'.ker := by rw [htop]; exact Subgroup.mem_top y
    rw [MonoidHom.mem_ker] at hx hy
    rw [hx, hy] at hab
    exact hab rfl
  have hker : π'.ker ≤ Subgroup.center ↥(modO2Image Y KY) :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hqbar inferInstance).resolve_left hne
  have hc : FFB.CmpHyp (modO2Image Y KY) ↥(autOn KY U) :=
    { quasi := hqbar
      center_odd := by
        rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
        exact hodd
      map := ⟨π', hπ's, hker, hne⟩
      list := hlist
      quasiX := hqA
      dvd60 := h60 }
  refine ⟨hqKY, hqA, hlist, h60, ⟨π, hπ⟩, ?_⟩
  rcases hc.cmp h314 h314bar hlt' with hL | hL | hL | hA7
  · exact Or.inl (IsSL3.of_mulEquiv e.symm hL)
  · exact Or.inr (Or.inl (IsPSp4.of_mulEquiv e.symm hL))
  · exact Or.inr (Or.inr (Or.inl (IsG2.of_mulEquiv e.symm hL)))
  · exact Or.inr (Or.inr (Or.inr hA7))

end CFSG.Quasithin.H13.Ch9.KGFF
