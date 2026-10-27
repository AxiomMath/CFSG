module

public import CFSG.Quasithin.Vol2.Ch9Sec2Qh
public import CFSG.Quasithin.Vol2.Ch7Lem734Wr
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318T
public import CFSG.Quasithin.Vol2.Ch9Sec2B69
public import CFSG.Quasithin.Vol2.Ch9Sec2Par

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits Vol2.Ch10.SecA

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian2_autI_of_comm {V X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXc : ∀ b ∈ X, ∀ b' ∈ X, b * b' * b⁻¹ * b'⁻¹ ∈ Subgroup.centralizer (V : Set G))
    (hXs : ∀ b ∈ X, b ^ 2 ∈ Subgroup.centralizer (V : Set G)) : IsElemAbelian2 (autI hV X) := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨g, hgX, rfl⟩ := (mem_autI hV).mp hx
    obtain ⟨h, hhX, rfl⟩ := (mem_autI hV).mp hy
    have h1 : convI hV (g * h * g⁻¹ * h⁻¹) = 1 :=
      (convI_eq_one_iff hV _).mpr (by simpa using hXc g hgX h hhX)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc convI hV g * convI hV h
        = (convI hV g * convI hV h * (convI hV g)⁻¹ * (convI hV h)⁻¹) *
            (convI hV h * convI hV g) := by group
      _ = convI hV h * convI hV g := by rw [h1, one_mul]
  · obtain ⟨g, hgX, rfl⟩ := (mem_autI hV).mp hx
    rw [← map_pow]
    exact (convI_eq_one_iff hV _).mpr (by simpa using hXs g hgX)

variable {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem sup_inf_centralizer_zQ_le (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) :
    (fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer (zQ T I : Set G) ≤
      T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
  (inf_le_inf_left _ (Subgroup.centralizer_le S.fsuV_le_zQ)).trans
    (S.sup_inf_centralizer_le h37c h38c)

theorem commutator_zQ_le (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (hB : B69One)
    (hq : qhatInt (fsuL0 T L ⊔ T) (zQ T I) (isElemAbelian_zQ T I) ≤ 2) :
    ∀ u ∈ zQ T I, ∀ g ∈ fsuL0 T L, g * u * g⁻¹ * u⁻¹ ∈ fsuV T I := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  push Not at hnot
  have hU := isElemAbelian_zQ T I
  have hU2 : IsPGroup 2 ↥(zQ T I) := B2F.isPGroup_of_isElemAbelian hU
  have hV2 : IsPGroup 2 ↥(fsuV T I) := S.isPGroup_fsuV
  have hUN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (zQ T I : Set G) := S.L0T_le_normalizer_zQ
  have hCQ := S.centralizerMod_le_Q h37c h38c hnot
  have hQL0T : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ fsuL0 T L ⊔ T :=
    inf_le_left.trans le_sup_right
  have hQU := Q_le_centralizer_zQ T I
  have hq' : kq (autI hU (fsuL0 T L ⊔ T)) 3 ≤ ((2 : ℚ) : WithTop ℚ) := by
    have h2 : ((2 : ℚ) : WithTop ℚ) = 2 := rfl
    rw [h2]
    exact hq
  obtain ⟨A, hA, -, hAr⟩ := kq_le_iff.mp hq'
  have hAr' : rkIdx (fixV A) ≤ 2 * rk A := by
    have hpos : (0 : ℚ) < (rk A : ℚ) := by exact_mod_cast hA.2.2.rk_pos hA.2.1
    unfold rAV at hAr
    rw [div_le_iff₀ hpos] at hAr
    exact_mod_cast hAr
  set At := preI hU (fsuL0 T L ⊔ T) hUN A with hAtdef
  have hAtL : At ≤ fsuL0 T L ⊔ T := preI_le hU
  have hAtN : At ≤ Subgroup.normalizer (zQ T I : Set G) := hAtL.trans hUN
  have hautAt : autI hU At = A := autI_preI hU hA.1
  have hQAt : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ At := fun q hq =>
    inf_centralizer_le_preI hU ⟨hQL0T hq, hQU hq⟩
  have hconv : ∀ b (hb : b ∈ At), convI hU ⟨b, hAtN hb⟩ ∈ A := fun b hb => by
    obtain ⟨hg, h⟩ := (mem_preI hU).mp hb
    exact h
  have hAtc : ∀ b ∈ At, ∀ b' ∈ At, b * b' * b⁻¹ * b'⁻¹ ∈
      Subgroup.centralizer (zQ T I : Set G) := by
    intro b hb b' hb'
    have h1 := hA.2.2.1 _ (hconv b hb) _ (hconv b' hb')
    have h2 : convI hU (⟨b, hAtN hb⟩ * ⟨b', hAtN hb'⟩ * ⟨b, hAtN hb⟩⁻¹ * ⟨b', hAtN hb'⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    simpa using (convI_eq_one_iff hU _).mp h2
  have hAts : ∀ b ∈ At, b ^ 2 ∈ Subgroup.centralizer (zQ T I : Set G) := by
    intro b hb
    have h2 : convI hU (⟨b, hAtN hb⟩ ^ 2) = 1 := by
      rw [map_pow]
      exact hA.2.2.2 _ (hconv b hb)
    simpa using (convI_eq_one_iff hU _).mp h2
  have hAtCU : At ⊓ Subgroup.centralizer (zQ T I : Set G) =
      T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
    le_antisymm ((inf_le_inf_right _ hAtL).trans (S.sup_inf_centralizer_zQ_le h37c h38c))
      (le_inf hQAt hQU)
  have hAtCV : At ⊓ Subgroup.centralizer (fsuV T I : Set G) =
      T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
    le_antisymm ((inf_le_inf_right _ hAtL).trans (S.sup_inf_centralizer_le h37c h38c))
      (le_inf hQAt inf_le_right)
  have hAtQ : ¬ At ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    intro hle
    apply hA.2.1
    rw [← hautAt, eq_bot_iff]
    intro x hx
    obtain ⟨g, hgA, rfl⟩ := (mem_autI hU).mp hx
    exact (convI_eq_one_iff hU g).mpr (hQU (hle hgA))
  have hrk : rk A = E3.mQuot At (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
    rw [← hautAt, E3.rk_autI_eq_mQuot hU hAtN, hAtCU]
  have hrkIdx :
      rkIdx (fixV A) = E3.mQuot (zQ T I) (zQ T I ⊓ Subgroup.centralizer (At : Set G)) := by
    rw [← hautAt]
    exact E3.rkIdx_fixV_autI hU hAtN
  have hcardA : (T ⊓ Subgroup.centralizer (fsuV T I : Set G)).relIndex At = 2 ^ rk A := by
    rw [← B1.card_elemAbelian hA.2.2, ← hautAt, ← hAtCU, ← card_autI_eq hU hAtN]
  have hbV : rk A + 1 ≤ E3.mQuot (fsuV T I) (fsuV T I ⊓ Subgroup.centralizer (At : Set G)) := by
    have hAtNV : At ≤ Subgroup.normalizer (fsuV T I : Set G) := hAtL.trans S.hN
    have hnFF := not_isFFModule_of_hyp702A S.hyp S.hV S.hNM
    have hBe : IsElemAbelian2 (autI S.hV At) :=
      isElemAbelian2_autI_of_comm S.hV
        (fun b hb b' hb' => Subgroup.centralizer_le S.fsuV_le_zQ (hAtc b hb b' hb'))
        (fun b hb => Subgroup.centralizer_le S.fsuV_le_zQ (hAts b hb))
    have hB1 : autI S.hV At ≠ ⊥ := by
      rw [Ne, autI_eq_bot_iff S.hV hAtNV]
      intro hle
      exact hAtQ (hAtCV ▸ le_inf le_rfl hle)
    have hlt : ¬ rkIdx (fixV (autI S.hV At)) ≤ rk (autI S.hV At) := fun hle =>
      hnFF ⟨autI S.hV At, autI_mono S.hV le_top, hB1, hBe,
        (B1.card_le_iff IntMod.sq_eq_one hBe).mpr hle⟩
    rw [E3.rkIdx_fixV_autI S.hV hAtNV, E3.rk_autI_eq_mQuot S.hV hAtNV, hAtCV, ← hrk] at hlt
    omega
  have hbW : 2 ^ rk A ≤
      (centralizerMod (fsuV T I) (zQ T I) At).relIndex (zQ T I) := by
    have hmp := S.minParabolic h37c h38c
    have hsqtk : IsSQTKSub (fsuL0 T L ⊔ T) := by
      refine isSQTKSub_of_inH S.hyp.fsu.qtke S.hyp.fsu.simple S.hyp.fsu.nonabelian
        (T := T) ⟨le_sup_right, fun h0 => S.fsuV_ne_bot ?_⟩
      rw [eq_bot_iff, ← h0, S.hQ]
      exact S.fsuV_le_Q
    have hQC : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤
        centralizerMod (fsuV T I) (fsuL0 T L ⊔ T) (zQ T I) := fun q hq =>
      ⟨hQL0T hq, S.T_le_normalizer_V hq.1, fun u hu => by
        rw [(Subgroup.mem_centralizer_iff.mp (hQU hq) u hu).symm, mul_inv_cancel_right,
          mul_inv_cancel]
        exact (fsuV T I).one_mem⟩
    have hCM : centralizerMod (fsuV T I) (fsuL0 T L ⊔ T) (zQ T I) ≤
        (fsuL0 T L ⊔ T) ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) :=
      hCQ.trans (inf_le_left.trans hmp.le)
    have hred : ∀ D : Subgroup G, D ≤ fsuL0 T L ⊔ T →
        fsuL0 T L ⊔ T ≤ Subgroup.normalizer (D : Set G) →
        (∀ d ∈ D, ∃ k : ℕ, d ^ (2 ^ k) ∈ centralizerMod (fsuV T I) (fsuL0 T L ⊔ T) (zQ T I)) →
        D ≤ centralizerMod (fsuV T I) (fsuL0 T L ⊔ T) (zQ T I) := by
      intro D hDH hHD hD
      have hD2 : IsPGroup 2 D := by
        intro d
        obtain ⟨k, hk⟩ := hD d d.2
        obtain ⟨j, hj⟩ := S.isPGroup_Q ⟨_, hCQ hk⟩
        refine ⟨k + j, Subtype.ext ?_⟩
        have hj' : ((d : G) ^ 2 ^ k) ^ 2 ^ j = 1 := congrArg Subtype.val hj
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        rw [pow_add, pow_mul]
        exact hj'
      have h1 := le_pCoreOf_of_le_normalizer 2 hDH hHD hD2
      rw [S.hQ] at h1
      exact h1.trans hQC
    have h := relIndex_le_of_b69One hB hmp hsqtk hU S.fsuV_le_zQ S.hN hUN hCM hred hAtL hAtc hAts
    have hcm : centralizerMod (fsuV T I) At (zQ T I) =
        T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
      le_antisymm (le_trans (fun x hx => ⟨hAtL hx.1, hx.2.1, hx.2.2⟩ :
          centralizerMod (fsuV T I) At (zQ T I) ≤
            centralizerMod (fsuV T I) (fsuL0 T L ⊔ T) (zQ T I)) hCQ)
        fun q hq => ⟨hQAt hq, (hQC hq).2.1, (hQC hq).2.2⟩
    rw [hcm, hcardA] at h
    exact h
  have hfil := relIndex_mul_relIndex_le S.fsuV_le_zQ (hAtL.trans S.hN)
    ((zQ_le_Q T I).trans (inf_le_left.trans S.T_le_normalizer_V))
  rw [E3.relIndex_eq_two_pow hV2, E3.relIndex_eq_two_pow hU2, E3.relIndex_eq_two_pow hU2] at hfil
  rw [E3.relIndex_eq_two_pow hU2] at hbW
  have h1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hbW
  rw [← pow_add] at hfil
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hfil
  rw [hrkIdx] at hAr'
  omega

theorem hyp318_zQ (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) :
    Hyp318 T (fsuM T L) (fsuL0 T L) (zQ T I) :=
  { inM := ⟨S.uniq.1.1, le_sup_right.trans S.uniq.1.2⟩
    nonempty := ⟨H, hH⟩
    perfect := fsuL0_eq_oTwoUpper S.hyp.fsu
    le_M := Subgroup.le_normalizer
    normal := le_rfl
    unique := S.L0_sup_T ▸ S.uniq
    reduced := S.isTwoReducedIn_zQ h37c h38c
    centralizer := by rw [S.inf_centralizer_zQ, S.hQ] }

theorem zQ_eq (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h316 : Theorem316Statement) (hB : B69One)
    (hH : ∃ H : Subgroup G, IsHStar T (fsuM T L) H) : zQ T I = fsuV T I := by
  obtain ⟨H, hH⟩ := hH
  have h318 := S.hyp318_zQ h37c h38c hH
  have hq := theorem318_one_of_316 h316 S.hyp.fsu.simple S.hyp.fsu.nonabelian S.hyp.fsu.qtke
    S.hyp.fsu.sylow h318
  have hZ : centerOf (fsuL0 T L ⊔ T) = ⊥ := by
    rcases theorem318_three hC58 h317 S.hyp.fsu.simple S.hyp.fsu.nonabelian S.hyp.fsu.qtke
        S.hyp.fsu.sylow h318 with ⟨hJ, -⟩ | ⟨-, -, hZ⟩
    · exfalso
      refine hJ (le_inf (iSup₂_le fun A hA => hA.1) ?_)
      exact fun x hx => Q_le_centralizer_zQ T I ⟨(iSup₂_le fun A hA => hA.1 : thompsonJ T ≤ T) hx,
        S.hJ hx⟩
    · exact hZ
  exact S.zQ_eq_of_commutator_le h37c h38c hZ (S.commutator_zQ_le h37c h38c hB hq)

theorem omegaOneCenter_le (h1 : zQ T I = fsuV T I) {S' : Subgroup G}
    (hQS : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ S') (hST : S' ≤ T) :
    omegaOneCenterOf S' ≤ fsuV T I ⊓ Subgroup.centralizer (S' : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨⟨hxS, hxC⟩, hx2⟩
  have hxQ : x ∈ T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
    ⟨hST hxS, Subgroup.centralizer_le (S.fsuV_le_Q.trans hQS) hxC⟩
  have hxZ : x ∈ zQ T I := Subgroup.subset_closure
    ⟨⟨hxQ, Subgroup.centralizer_le hQS hxC⟩, hx2⟩
  exact ⟨h1 ▸ hxZ, hxC⟩

theorem omegaOneCenter_T_eq (h1 : zQ T I = fsuV T I) :
    quasithinOmegaOneCenter T = fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
  refine le_antisymm (S.omegaOneCenter_le h1 inf_le_left le_rfl) ?_
  rintro x ⟨hxV, hxC⟩
  exact Subgroup.subset_closure ⟨⟨S.fsuV_le_T hxV, hxC⟩, S.hV.2 x hxV⟩

theorem omegaOneCenter_T_le (h1 : zQ T I = fsuV T I) :
    quasithinOmegaOneCenter T ≤ fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) :
      Set G) := by
  rw [S.omegaOneCenter_T_eq h1]
  exact inf_le_inf_left _ (Subgroup.centralizer_le inf_le_left)

end Setup

end CFSG.Quasithin.H13.Ch9
