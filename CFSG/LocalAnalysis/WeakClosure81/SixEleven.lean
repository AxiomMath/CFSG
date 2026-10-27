module

public import CFSG.Quasithin.Background.E3Prop

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G] [Finite G]
variable {V : Subgroup G}

theorem omegaOneCenterOf_isElemAbelian (X : Subgroup G) :
    IsElemAbelian 2 (omegaOneCenterOf X) := by
  rw [omegaOneCenterOf, omegaOneOf]
  refine B2F.isElemAbelian_closure ?_ ?_
  · rintro a ⟨ha, -⟩ b ⟨hb, -⟩
    exact Subgroup.mem_centralizer_iff.1 hb.2 a ha.1
  · rintro a ⟨-, ha2⟩
    exact ha2

theorem omegaOneCenter_le_center_pCoreOf {H S : Subgroup G}
    (hF : CFSG.QuasithinUnique.CharTwo H) (hS : IsSylowIn 2 S H) :
    omegaOneCenterOf S ≤ centerOf (pCoreOf 2 H) := by
  have hF' : H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H := hF
  rw [omegaOneCenterOf, omegaOneOf, Subgroup.closure_le]
  rintro x ⟨hx, -⟩
  have hxS : x ∈ S := hx.1
  have hxCS : x ∈ Subgroup.centralizer (S : Set G) := hx.2
  have hPH : pCoreOf 2 H ≤ S := E1.pCoreOf_two_le_of_isSylowIn hS
  have hxC : x ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
    Subgroup.centralizer_le hPH hxCS
  exact Subgroup.mem_inf.2 ⟨hF' (Subgroup.mem_inf.2 ⟨hS.le hxS, hxC⟩), hxC⟩

theorem omegaOneCenter_conjClosure_isElemAbelian {H S : Subgroup G}
    (hF : CFSG.QuasithinUnique.CharTwo H) (hS : IsSylowIn 2 S H) :
    IsElemAbelian 2 (conjClosure (omegaOneCenterOf S) H) := by
  set Z := omegaOneCenterOf S with hZ
  set U := conjClosure Z H with hU
  have hZctr : Z ≤ centerOf (pCoreOf 2 H) := omegaOneCenter_le_center_pCoreOf hF hS
  have hZab : IsElemAbelian 2 Z := omegaOneCenterOf_isElemAbelian S
  have hcenterNorm : H ≤ Subgroup.normalizer (centerOf (pCoreOf 2 H) : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H).trans
      (E3.normalizer_le_normalizer_centerOf (pCoreOf 2 H))
  have hmem : ∀ h ∈ H, ∀ z ∈ Z, h * z * h⁻¹ ∈ centerOf (pCoreOf 2 H) := fun h hh z hz =>
    ((Subgroup.mem_normalizer_iff.1 (hcenterNorm hh)) z).1 (hZctr hz)
  rw [hU, conjClosure]
  refine B2F.isElemAbelian_closure ?_ ?_
  · rintro a ⟨h₁, hh₁, z₁, hz₁, rfl⟩ b ⟨h₂, hh₂, z₂, hz₂, rfl⟩
    exact Subgroup.mem_centralizer_iff.1 (hmem h₂ hh₂ z₂ hz₂).2
      (h₁ * z₁ * h₁⁻¹) (hmem h₁ hh₁ z₁ hz₁).1
  · rintro a ⟨h₁, hh₁, z₁, hz₁, rfl⟩
    have hz1 : z₁ ^ 2 = 1 := hZab.2 z₁ hz₁
    have hconj : (h₁ * z₁ * h₁⁻¹) ^ 2 = h₁ * z₁ ^ 2 * h₁⁻¹ := by
      rw [pow_two, pow_two]
      group
    rw [hconj, hz1, mul_one]
    group

theorem six_eleven_one_generic (hV : IsElemAbelian 2 V) {H S U Z : Subgroup G}
    (hS : IsSylowIn 2 S H)
    (hUn : H ≤ Subgroup.normalizer (U : Set G)) (hU : IsElemAbelian 2 U)
    (hZU : Z ≤ U) {i : ℕ}
    (hi : i < E3.sParam hV - E3.aParam (autI hU H)) :
    ⁅E3.wClos V i S, U⁆ = ⊥ ∧
      (H : Set G) = ((H ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) : Set G) *
        ((H ⊓ Subgroup.normalizer (E3.wClos V i S : Set G) : Subgroup G) : Set G) := by
  have hcomm : ⁅E3.wClos V i S, U⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact E3.e3_18_comm hV hS.le hUn hU hi
  refine ⟨hcomm, ?_⟩
  have hCN : H ⊓ Subgroup.centralizer (U : Set G) ≤ H ⊓ Subgroup.centralizer (Z : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le hZU)
  have hfac := E3.e3_18_factor hV hS hUn hU hi
  refine Set.Subset.antisymm ?_ ?_
  · intro h hh
    obtain ⟨c, hc, n, hn, hcn⟩ := hfac h hh
    exact Set.mem_mul.2 ⟨c, hCN hc, n, hn, hcn.symm⟩
  · refine Subgroup.mul_subset (fun x hx => (inf_le_left : H ⊓ _ ≤ H) hx)
      (fun x hx => (inf_le_left : H ⊓ _ ≤ H) hx)

theorem six_eleven_one (hV : IsElemAbelian 2 V) {H S : Subgroup G}
    (hF : CFSG.QuasithinUnique.CharTwo H) (hS : IsSylowIn 2 S H) {i : ℕ}
    (hi : i < E3.sParam hV -
      E3.aParam (autI (omegaOneCenter_conjClosure_isElemAbelian hF hS) H)) :
    ⁅E3.wClos V i S, conjClosure (omegaOneCenterOf S) H⁆ = ⊥ ∧
      (H : Set G) =
        ((H ⊓ Subgroup.centralizer (omegaOneCenterOf S : Set G) : Subgroup G) : Set G) *
          ((H ⊓ Subgroup.normalizer (E3.wClos V i S : Set G) : Subgroup G) : Set G) :=
  six_eleven_one_generic (U := conjClosure (omegaOneCenterOf S) H) (Z := omegaOneCenterOf S)
    hV hS (le_normalizer_conjClosure _ _) (omegaOneCenter_conjClosure_isElemAbelian hF hS)
    (le_conjClosure _ _) hi

theorem six_eleven_three (hV : IsElemAbelian 2 V) {H S : Subgroup G}
    (hS : IsSylowIn 2 S H) {i j : ℕ} (hInE : E1.InE j H)
    (hij : i + j < E3.sParam hV) :
    (H ⊓ Subgroup.centralizer (E3.cClos V (i + j) S : Set G)) ⊔
      (H ⊓ Subgroup.normalizer (E3.wClos V i S : Set G)) = H := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
  have hEF := (E1.inE_iff_inEFor hS).1 hInE (E3.gammaSet V i H)
    (E3.isInvColl_gammaSet hV i H)
  rw [E3.weakClosure_gammaSet hS.le] at hEF
  have hE : E1.eGen j H S (E3.gammaSet V i H) ≤
      (H ⊓ Subgroup.centralizer (E3.cClos V (i + j) S : Set G)) ⊔
        (H ⊓ Subgroup.normalizer (E3.wClos V i S : Set G)) := by
    refine iSup₂_le fun A hA => iSup_le fun hAS => iSup₂_le fun K hK => ?_
    have hAΓ : A ∈ E3.gammaSet V i S := ⟨hAS, hA.2⟩
    have hSK : IsSylowIn 2 (S ⊓ K) K := hK.2.2.1
    have hKeq : K = (S ⊓ K) ⊔ twoResidual K := (sup_twoResidual_eq hSK).symm
    have hcomm := E3.e3_19_comm hV hS hij hAΓ hK
    have hSN : S ≤ Subgroup.normalizer (E3.wClos V i S : Set G) :=
      Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos S)
    have h1 : S ⊓ K ≤ H ⊓ Subgroup.normalizer (E3.wClos V i S : Set G) :=
      le_inf (inf_le_right.trans hK.1) (inf_le_left.trans hSN)
    have h2 : twoResidual K ≤ H ⊓ Subgroup.centralizer (E3.cClos V (i + j) S : Set G) :=
      le_inf ((twoResidual_le K).trans hK.1)
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm)
    rw [hKeq]
    exact sup_le (h1.trans le_sup_right) (h2.trans le_sup_left)
  calc H = E1.eGen j H S (E3.gammaSet V i H) ⊔
        (H ⊓ Subgroup.normalizer (E3.wClos V i S : Set G)) := hEF.symm
    _ ≤ _ := sup_le hE le_sup_right

end CFSG.LocalAnalysis.WeakClosure81

end
