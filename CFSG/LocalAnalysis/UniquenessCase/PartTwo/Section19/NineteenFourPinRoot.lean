module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourPinOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34InvolCentFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourInnerTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem pin_one_U34_19 (D : Data G)
    (hSg : UC6S846.SigmaStd D) (hU5 : Inputs1719.K_U34InvolCentFive)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hm : 4 < mSub V₀)
    (hN2 : ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M) {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hLN : (L.subgroupOf D.M).Normal)
    (hU3 : IsU3 (Bar2 L) 2) (hLA : ¬ ⁅L, A⁆ ≤ pCoreOf 2 D.M)
    (hq : E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ D.T)) = 1)
    (hin : A ≤ (D.T ⊓ L) ⊔ pCoreOf 2 (L ⊔ D.T)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hTN : D.T ≤ Subgroup.normalizer (L : Set G) :=
    D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLN)
  let H : Subgroup G := L ⊔ D.T
  let Q : Subgroup G := pCoreOf 2 H
  have hqH : E3.mQuot A (A ⊓ Q) = 1 := hq
  have hAgamma : A ∈ E3.gammaSet V₀ 0 D.T := hA
  obtain ⟨hAT, gA, hAg, -⟩ := hA
  have hAel : IsElemAbelian 2 A :=
    CFSG.Quasithin.B2F.isElemAbelian_mono hAg
      (E3.isElemAbelian_conjSubgroup h.hyp.hyp125.pairFacts.elemAbelian₀ gA)
  have hAM : ¬ A ≤ pCoreOf 2 D.M := by
    intro hle
    apply hLA
    have hLN' : L ≤ Subgroup.normalizer (pCoreOf 2 D.M : Set G) :=
      hLM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
    have hcalc : ⁅L, pCoreOf 2 D.M⁆ ≤ pCoreOf 2 D.M := by
      rw [Subgroup.commutator_comm]
      exact CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer hLN'
    exact (Subgroup.commutator_mono le_rfl hle).trans hcalc
  have hAQ : ¬ A ≤ Q := by
    intro hle
    have h0 : E3.mQuot A (A ⊓ Q) = 0 := by rw [inf_eq_left.mpr hle, E3.mQuot_self]
    omega
  have hHM : H ≤ D.M := sup_le hLM D.sylowM.le
  have hQH : Q ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hTsyl : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D le_sup_right
  have hQT : Q ≤ D.T := CFSG.Quasithin.RonanD33.pCoreOf_le_of_sylow le_sup_right
    D.sylowM.isPGroup hTsyl.2.2
  have hAH : A ≤ H := hAT.trans le_sup_right
  have hC2 : E3.cClos V₀ 2 D.T ≤ H :=
    fun x hx => Subgroup.mem_sup_right (Subgroup.mem_inf.mp hx).1
  have h5sig : 5 ∈ D.sig := h.p_eq ▸ h.hyp.hp
  have hsp : IsStronglyPEmbedded 5 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC h.hyp.hL.1) h5sig
  have hP5 : ∀ N : Subgroup G, N ≤ H → H ≤ Subgroup.normalizer (N : Set G) →
      ¬ N ≤ Q → 5 ∣ Nat.card N := by
    intro N hNH hHN hNQ
    have hJs : IsSimpleGroup (Bar2 L) := isSimpleGroup_bar2_of_shape (Or.inr hU3)
    have hLNle : L ≤ N := le_of_normal_of_isSimple_19 hJs h.hyp.hL.1.2.1
      D.sylowM.isPGroup hTN
      (fun y hy hyN hρ => mem_pCoreOf_of_rhoL_eq_one_of_isU3_19 hU3 hy hyN hρ)
      hNH hHN hNQ
    exact ((h.p_eq ▸ h.hyp.hL.2 : 5 ∈ piSet L).2).trans (Subgroup.card_dvd_of_le hLNle)
  have hZ : A ⊓ centerOf (E3.wClos V₀ 2 Q) ≠ ⊥ :=
    inf_centerOf_wClos_two_ne_bot_19 h.hyp.hyp125 hm hsp hN2 hHM hQH hHQ hQT hAH hAgamma hAM
      hAQ (by rw [hqH]; norm_num) hC2 hP5
  obtain ⟨v, hvA, hvQ⟩ := SetLike.not_le_iff_exists.mp hAQ
  have hvv : v * v = 1 := by simpa [pow_two] using hAel.2 v hvA
  have hQn : Q ≤ Subgroup.normalizer ((D.T ⊓ L : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨hxT, hxL⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hQT hq)) x).mp hxT,
          (Subgroup.mem_normalizer_iff.mp (hTN (hQT hq)) x).mp hxL⟩
    · intro hx
      obtain ⟨hxT, hxL⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hQT hq)) x).mpr hxT,
          (Subgroup.mem_normalizer_iff.mp (hTN (hQT hq)) x).mpr hxL⟩
  have hvmul : v ∈ (((D.T ⊓ L) ⊔ Q : Subgroup G) : Set G) := hin hvA
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (D.T ⊓ L) Q hQn] at hvmul
  obtain ⟨u, huTL, q, hqQ, huq⟩ := hvmul
  have huL : u ∈ L := (Subgroup.mem_inf.mp huTL).2
  have huH : u ∈ H := Subgroup.mem_sup_left huL
  have hO2LQ : pCoreOf 2 L ≤ Q :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 le_sup_left
      (sup_le Subgroup.le_normalizer hTN)
  have hLQ : L ⊓ Q ≤ pCoreOf 2 L := CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 le_sup_left
  have huu : u * u ∈ pCoreOf 2 L := by
    have hu : u = v * q⁻¹ := eq_mul_inv_of_mul_eq huq
    have h1 : v * q⁻¹ * v⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hHQ (hAH hvA)) q⁻¹).mp (Q.inv_mem hqQ)
    have h2 : u * u = (v * q⁻¹ * v⁻¹) * (v * v) * q⁻¹ := by rw [hu]; group
    have h3 : u * u ∈ Q := by
      rw [h2, hvv, mul_one]
      exact Q.mul_mem h1 (Q.inv_mem hqQ)
    exact hLQ (Subgroup.mem_inf.mpr ⟨L.mul_mem huL huL, h3⟩)
  let uL : ↥L := ⟨u, huL⟩
  have hubar : (uL : Bar2 L) * (uL : Bar2 L) = 1 := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact (CFSG.mem_openPCoreOf_iff (uL * uL)).mp huu
  obtain ⟨xbar, hxo, hxc⟩ := hU5 (Bar2 L) hU3 (uL : Bar2 L) hubar
  obtain ⟨xL, rfl⟩ := QuotientGroup.mk_surjective xbar
  have hxH : (xL : G) ∈ H := Subgroup.mem_sup_left xL.2
  have hx5 : (xL : G) ^ 5 ∈ Q := by
    have h1 : ((xL ^ 5 : ↥L) : Bar2 L) = 1 := by
      rw [QuotientGroup.mk_pow, ← hxo, pow_orderOf_eq_one]
    rw [QuotientGroup.eq_one_iff] at h1
    have h2 := (CFSG.mem_openPCoreOf_iff (xL ^ 5)).mpr h1
    rw [Subgroup.coe_pow] at h2
    exact hO2LQ h2
  have hxQ : (xL : G) ∉ Q := by
    intro hxQ
    have h1 : (xL : G) ∈ pCoreOf 2 L := hLQ (Subgroup.mem_inf.mpr ⟨xL.2, hxQ⟩)
    have h2 : ((xL : ↥L) : Bar2 L) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ((CFSG.mem_openPCoreOf_iff xL).mp h1)
    rw [h2, orderOf_one] at hxo
    omega
  have hux : u * (xL : G) * u⁻¹ * (xL : G)⁻¹ ∈ pCoreOf 2 L := by
    have h1 : ((uL * xL * uL⁻¹ * xL⁻¹ : ↥L) : Bar2 L) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, ← hxc]
      group
    rw [QuotientGroup.eq_one_iff] at h1
    exact (CFSG.mem_openPCoreOf_iff _).mpr h1
  have hvx : v * (xL : G) * v⁻¹ * (xL : G)⁻¹ ∈ Q := by
    rw [← huq]
    have h1 : (xL : G) * q⁻¹ * (xL : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hHQ hxH) q⁻¹).mp (Q.inv_mem hqQ)
    have h2 : q * ((xL : G) * q⁻¹ * (xL : G)⁻¹) ∈ Q := Q.mul_mem hqQ h1
    have h3 : u * (q * ((xL : G) * q⁻¹ * (xL : G)⁻¹)) * u⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hHQ huH) _).mp h2
    have h5 : u * q * (xL : G) * (u * q)⁻¹ * (xL : G)⁻¹ =
        (u * (q * ((xL : G) * q⁻¹ * (xL : G)⁻¹)) * u⁻¹) *
          (u * (xL : G) * u⁻¹ * (xL : G)⁻¹) := by group
    rw [h5]
    exact Q.mul_mem h3 (hO2LQ hux)
  exact false_of_commutator_mem_pCoreOf_19 h.hyp.hyp125 hm hsp hHM hAgamma hAM hAH hZ hvA hvQ
    hxH hxQ hx5 hvx

theorem gap19_4_PinRoot_holds
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (D : Data G) (h66 : UC6.R6_6 D) (h88 : W3Thm88 G) (hSg : UC6S846.SigmaStd D)
    (h8107 : F08.R8107 D) (hU : Inputs1719.K_U34OuterInv)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (h93 : Thm93 V₀ D.T) : Gap19_4_PinRoot D V₀ V p L K h := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hm _h2 _h3 hN2 A hA J hJ hAS hJA _hJC hO hq _hres hdisj
  have hAgamma : A ∈ E3.gammaSet V₀ 0 D.T := hA
  have hAT : A ≤ D.T := hA.1
  have hLc : L ∈ calC D.M := h.hyp.hL.1
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have h5sig : 5 ∈ D.sig := h.p_eq ▸ h.hyp.hp
  have hsp : IsStronglyPEmbedded 5 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC h.hyp.hL.1) h5sig
  have hO2L : pCoreOf 2 L ≤ pCoreOf 2 D.M := UC22.P22s.pCoreOf_le_of_isSubnormal hLc.1
  have hO2K : pCoreOf 2 K ≤ pCoreOf 2 D.M := UC22.P22s.pCoreOf_le_of_isSubnormal h.hK.1
  have hJM : J ≤ D.M := by
    rcases hJ with ⟨rfl | rfl, -⟩ | ⟨rfl, -⟩
    · exact hLM
    · exact hKM
    · exact sup_le hLM hKM
  have hAM : ¬ A ≤ pCoreOf 2 D.M := by
    intro hle
    apply hJA
    have hJN : J ≤ normalizer (pCoreOf 2 D.M : Set G) :=
      hJM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
    have hcalc : ⁅J, pCoreOf 2 D.M⁆ ≤ pCoreOf 2 D.M := by
      rw [Subgroup.commutator_comm]
      exact CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer hJN
    exact (Subgroup.commutator_mono le_rfl hle).trans hcalc
  by_cases hLN : (L.subgroupOf D.M).Normal
  ·
    have hJ' : J = L ∨ J = K := by
      rcases hJ with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact h1
      · exact absurd hLN h2
    have hKN : (K.subgroupOf D.M).Normal := normal_right_of_normal_left_19 h hLN
    have hTL : D.T ≤ normalizer (L : Set G) :=
      D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLN)
    have hTK : D.T ≤ normalizer (K : Set G) :=
      D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKN)
    have hFM : ∀ F : Subgroup G, F ≤ D.M → D.T ≤ normalizer (F : Set G) →
        ¬ ⁅F, A⁆ ≤ pCoreOf 2 F → ¬ ⁅F, A⁆ ≤ pCoreOf 2 D.M := by
      intro F hFM hTF hFA hle
      apply hFA
      have h1 : ⁅F, A⁆ ≤ F :=
        CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer (hAT.trans hTF)
      exact (le_inf h1 hle).trans (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hFM)
    have htriv : ∀ F : Subgroup G, ((J = L ∧ F = K) ∨ (J = K ∧ F = L)) →
        ⁅F, A⁆ ≤ pCoreOf 2 F → False := by
      intro F hJF hFA
      have hqLKT : E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T)) ≤ 2 :=
        (mQuot_LKT_le_of_trivial_19 h hLN hAT hJF hFA).trans (by rw [hq]; norm_num)
      have hJX : J ≤ L ⊔ K ⊔ D.T := by
        rcases hJF with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact le_sup_left.trans le_sup_left
        · exact le_sup_right.trans le_sup_left
      have hTJ : D.T ≤ normalizer (J : Set G) := by
        rcases hJF with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact hTL
        · exact hTK
      have hAQ : ¬ A ≤ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
        intro hle
        apply hJA
        have h1 : ⁅J, A⁆ ≤ J :=
          CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer (hAT.trans hTJ)
        have h2 : ⁅J, pCoreOf 2 (L ⊔ K ⊔ D.T)⁆ ≤ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
          rw [Subgroup.commutator_comm]
          exact CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer
            (hJX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
        have h3 : ⁅J, A⁆ ≤ pCoreOf 2 J :=
          (le_inf h1 ((Subgroup.commutator_mono le_rfl hle).trans h2)).trans
            (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hJX)
        rcases hJF with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact h3.trans hO2L
        · exact h3.trans hO2K
      have hF : F = L ∨ F = K := by
        rcases hJF with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact Or.inr rfl
        · exact Or.inl rfl
      exact false_of_trivial_factor_19 D hSg h hm hN2 hA hAM hAQ hqLKT hF hFA
    have hJLc : JChoice19 D L K L := Or.inl ⟨Or.inl rfl, hLN⟩
    have hJKc : JChoice19 D L K K := Or.inl ⟨Or.inr rfl, hLN⟩
    by_cases hU3 : IsU3 (Bar2 L) 2
    ·
      by_cases hLA : ⁅L, A⁆ ≤ pCoreOf 2 L
      · have hJK : J = K := by
          rcases hJ' with rfl | rfl
          · exact absurd (hLA.trans hO2L) hJA
          · rfl
        exact htriv L (Or.inr ⟨hJK, rfl⟩) hLA
      ·
        have hLAM : ¬ ⁅L, A⁆ ≤ pCoreOf 2 D.M := hFM L hLM hTL hLA
        by_cases hin : A ≤ (D.T ⊓ L) ⊔ pCoreOf 2 (L ⊔ D.T)
        · have hle2 := mQuot_le_two_U34_inner_19 D h hA hLN hU3 hin
          have hne0 := mQuot_ne_zero_19 D h hA hJLc hLAM
          by_cases h2 : E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ D.T)) = 2
          · obtain ⟨g, hg2, hg1⟩ :=
              pin_two_of_isU3_19 D hSg h hm hN2 hA hJLc hLAM h2 (Or.inl hin) rfl hU3
            exact hg1 (hO g hg2)
          · exact pin_one_U34_19 D hSg Inputs1719.k_U34InvolCentFive_holds h hm hN2 hA hLN
              hU3 hLAM (by omega) hin
        · obtain ⟨Y, hY⟩ := calP19_4_nonempty_of_outer_U34 hU D h hA hJLc ⟨rfl, hU3⟩ hin
          have hmem := calP19_4_subset_calPMTA D h8107 hsp h hJLc hY
          rw [calPMTA_eq_empty_19 hTim hcat D h66 h88 h.hyp.hyp125 hm h93 hA hAS] at hmem
          exact hmem
    ·
      have hLalt : IsAlt (Bar2 L) 5 := S17.isAlt_five_of_isL2_two (h.shape.resolve_right hU3)
      by_cases hLA : ⁅L, A⁆ ≤ pCoreOf 2 L
      · have hJK : J = K := by
          rcases hJ' with rfl | rfl
          · exact absurd (hLA.trans hO2L) hJA
          · rfl
        exact htriv L (Or.inr ⟨hJK, rfl⟩) hLA
      · by_cases hKA : ⁅K, A⁆ ≤ pCoreOf 2 K
        · have hJL : J = L := by
            rcases hJ' with rfl | rfl
            · rfl
            · exact absurd (hKA.trans hO2K) hJA
          exact htriv K (Or.inl ⟨hJL, rfl⟩) hKA
        ·
          have hLAM : ¬ ⁅L, A⁆ ≤ pCoreOf 2 D.M := hFM L hLM hTL hLA
          have hKAM : ¬ ⁅K, A⁆ ≤ pCoreOf 2 D.M := hFM K hKM hTK hKA
          have hL5 : ¬ (L = L ⊔ K ∨ (L = L ∧ IsU3 (Bar2 L) 2)) := by
            rintro (h1 | ⟨-, h1⟩)
            · exact (sup_ne_left_right_19 h).1 h1.symm
            · exact hU3 h1
          have hK5 : ¬ (K = L ⊔ K ∨ (K = L ∧ IsU3 (Bar2 L) 2)) := by
            rintro (h1 | ⟨h1, -⟩)
            · exact (sup_ne_left_right_19 h).2 h1.symm
            · exact h.hne h1
          have hmL2 := mQuot_le_two_19 D h hA hJLc hL5
          have hmK2 := mQuot_le_two_19 D h hA hJKc hK5
          have hmL0 := mQuot_ne_zero_19 D h hA hJLc hLAM
          have hmK0 := mQuot_ne_zero_19 D h hA hJKc hKAM
          by_cases hL2 : E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ D.T)) = 2
          · obtain ⟨g, hg2, hg1⟩ :=
              pin_two_of_isAlt_19 D hSg h hm hN2 hA ⟨Or.inl rfl, hLN⟩ hLalt hLAM hL2
            exact hg1 (hO g hg2)
          by_cases hK2 : E3.mQuot A (A ⊓ pCoreOf 2 (K ⊔ D.T)) = 2
          · obtain ⟨g, hg2, hg1⟩ :=
              pin_two_of_isAlt_19 D hSg h hm hN2 hA ⟨Or.inr rfl, hLN⟩ h.hKshape hKAM hK2
            exact hg1 (hO g hg2)
          exact pin_one_single_twoSided_19 D hSg h hm hN2 hA hLN hLalt (by omega) (by omega)
            hLA hKA
  ·
    have hJLK : J = L ⊔ K := by
      rcases hJ with ⟨-, h1⟩ | ⟨h2, -⟩
      · exact absurd h1 hLN
      · exact h2
    subst hJLK
    by_cases hAL : A ≤ normalizer (L : Set G)
    ·
      have hFA : ⁅L, A⁆ ≤ pCoreOf 2 L ∨ ⁅K, A⁆ ≤ pCoreOf 2 K := by
        rcases hdisj with h1 | h1 | h1
        · exact absurd h1 hLN
        · exact absurd hAL h1
        · exact h1
      have hAQ : ¬ A ≤ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
        intro hle
        have h0 : E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T)) = 0 := by
          rw [inf_eq_left.mpr hle, E3.mQuot_self]
        omega
      rcases hFA with hFA | hFA
      · exact false_of_trivial_factor_19 D hSg h hm hN2 hA hAM hAQ (by omega) (Or.inl rfl) hFA
      · exact false_of_trivial_factor_19 D hSg h hm hN2 hA hAM hAQ (by omega) (Or.inr rfl) hFA
    ·
      exact pin_one_swap_19 D hSg h hm hN2 hA hLN hJA hq hAL

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
