module

public import CFSG.Quasithin.Vol2.Ch9Sec3L34Chain
public import CFSG.Quasithin.Vol2.Ch9Sec3L34Cube
public import CFSG.Quasithin.Vol2.Ch9Sec3L34Max
public import CFSG.Quasithin.Vol2.Ch3xThm316

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem L34.not_isSolvable_of_le {K H : Subgroup G} (hKH : K ≤ H)
    (hKL : IsPSL 3 2 2 (O2Q K)) : ¬ Group.IsSolvable ↥H := by
  intro hsolv
  have : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKH)
  have : Group.IsSolvable (O2Q K) := inferInstance
  have hS : IsSimpleGroup (O2Q K) := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hKL).2
  obtain ⟨a, b, hab⟩ : ∃ a b : O2Q K, a * b ≠ b * a :=
    Vol2Native.A312L.Seven.nonabelian_of_card_not_prime (by
      rw [Ch1Four.card_of_isPSL_three_four hKL]; norm_num)
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)

namespace Setup

variable (S : Setup T L I n)
include S

theorem false_of_le_pCoreOf_l34 (hC58 : TheoremC58) (hD15 : D15AsPrintedSQTK)
    (hS316 : AS316SylowNonsolvable) (hKG : FactL34QuadThree)
    (hq : ∀ E₀ : Subgroup G, E₀ ≤ T → IsElemAbelian 2 E₀ → ⁅⁅fsuV T I, E₀⁆, E₀⁆ = ⊥ →
      ¬ E₀ ≤ Subgroup.centralizer (fsuV T I : Set G) →
      ((Subgroup.centralizer (fsuV T I : Set G)).relIndex E₀) ^ 4 ≤
        ((Subgroup.centralizer (E₀ : Set G)).relIndex (fsuV T I)) ^ 3)
    (hdual : ¬ IsDualFFInt (fsuL0 T L ⊔ T) (fsuV T I) S.hV)
    {H K : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hHK : H = K ⊔ T) (hKc : K ∈ cComp H)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hJ : IsPGroup 2 (kerIn (H ⊓ fsuM T L) H))
    (hKL : IsPSL 3 2 2 ↥(E2.star (H ⊓ fsuM T L) H K)) (hVH : fsuV T I ≤ pCoreOf 2 H) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  have hT := hfsu.sylow
  have hs := hfsu.simple
  have hnab := hfsu.nonabelian
  have hK := hfsu.qtke
  have hM : InM T (fsuM T L) := ⟨S.uniq.1.1, le_sup_right.trans S.uniq.1.2⟩
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hred : IsTwoReducedIn (fsuL0 T L ⊔ T) (fsuV T I) :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mpr ⟨S.hVLT, S.hRed⟩
  have h315 : Hyp315 T (fsuM T L) (fsuL0 T L ⊔ T) H (fsuV T I) :=
    { T_le := le_sup_right, le_M := Setup.L0T_le_fsuM, hStar := hH, reduced := hred,
      centralizer := S.hQ, «case» := Or.inr fun x hx => S.hMN hx.2 }
  have h1 : ¬ ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 (fsuL0 T L ⊔ T) ∧
      (fsuL0 T L ⊔ T) ⊔ H ≤ Subgroup.normalizer (R₀ : Set G) := by
    rintro ⟨R₀, hR₀, hR₀le, hR₀N⟩
    have hR₀2 : IsPGroup 2 R₀ := (pCoreOf_isPGroup 2 _).to_le hR₀le
    have hLT : L ⊔ T ≤ Subgroup.normalizer (R₀ : Set G) :=
      (sup_le_sup_right S.L_le_L0 T).trans (le_sup_left.trans hR₀N)
    exact hH.2.1 ((le_sup_right.trans hR₀N).trans (S.normalizer_le_of_le hR₀2 hR₀ hLT))
  have hV0 := S.fsuV_ne_bot
  have hD : D11Hyp (fsuL0 T L ⊔ T) H T (fsuV T I) (H ⊓ fsuM T L) :=
    h315.toHyp315Base.d11Hyp hT hV0 (noNormal_of_not_exists h1)
  have hnff : ¬ IsFFInt (fsuL0 T L ⊔ T) (fsuV T I) h315.reduced.2.2.1 := by
    rintro ⟨A, hA, hA1, hA2, hcard⟩
    exact not_isFFModule_of_hyp702A S.hyp S.hV S.hNM
      ⟨A, hA.trans (autOn_le_autOn _ le_top), hA1, hA2, hcard⟩
  have hsqH : IsSQTKSub H := isSQTKSub_of_inH hK hs hnab h315.inH_H
  have hKL' : IsPSL 3 2 2 (O2Q K) := L34.isPSL_of_star hKH hJ hKL
  rcases hD15 G _ H T _ (H ⊓ fsuM T L) hD hsqH with h1' | ⟨-, h2⟩ | h3 | ⟨-, -, c, hc, hser⟩ |
    ⟨h5a, h5b, -, -, -, -⟩
  · exact h1' hVH
  · exact hnff h2
  · exact hdual h3
  ·
    have hmp := hD.minParabolic hnff
    have hUT : conjClosure (fsuV T I) H ≤ T :=
      (conjClosure_le fun g hg v hv =>
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hg) v).mp (hVH hv)).trans
        (B6.pCoreOf_two_le_of_isSylowTwoOf hD.sylow₂)
    have hUe := D15Proof.isElemAbelian_conjClosure hD hnff hVH
    exact L34.false_of_chain_cube hD hnff hVH hq
      (fun L' N' hstep hnc A hAT hAe hquadN =>
        L34.cube_of_chief hKG hmp hUT hUe hKH hTK hHK hJ hKL' hstep hnc hAT hAe hquadN) hc hser
  ·
    have hsyl := hS316 G T (fsuM T L) _ H _ hs hnab hK hT hM h315 hV0 h1
      (fun hq1 => hnff ((isFFInt_iff_qInt_le_one _ _ _).mpr hq1)) hdual hVH h5a h5b
      (L34.not_isSolvable_of_le hKH hKL')
    exact h1 (h315.toHyp315Base.exists_normal_of_sylow hC58 hs hnab hK hT hM hsyl)

end Setup

end CFSG.Quasithin.H13.Ch9
