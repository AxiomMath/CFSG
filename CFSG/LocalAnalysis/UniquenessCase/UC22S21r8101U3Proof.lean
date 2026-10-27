module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101U3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101U3Fr
public import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclR3Basic
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101U3Syl
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101U3Cnt
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101U3Norm
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101U3Inv
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UIrr
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101USyl
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UCheap
import CFSG.LocalAnalysis.UniquenessCase.UC22S13a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3b
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Fusion
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Matrix
open CFSG.RepresentationTheory (IsIrreducibleMatrixRep)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

namespace U4P

variable {D : Data G} {L K : Subgroup G} {n p : ℕ}

theorem u81_dvd_of_inf_eq_bot (u : U4P D L K n p) {r : ℕ} (hr : r.Prime)
    (hrp : r ∣ 2 ^ p - 1) (hsp : IsStronglyPEmbedded p D.M) (hfour : 4 ≤ CFSG.Open.pRank p D.M)
    {R B : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R D.M) (hBR : B ≤ R)
    (hBel : IsElemAbelian r B) (hΩ : ∀ x ∈ R, x ^ r = 1 → x ∈ B)
    (hB0 : barImage D.M B ⊓ centralizer
      ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) = ⊥) :
    p ∣ Nat.card (centralizer (B : Set G)) := by
  obtain ⟨c, hcC, hco⟩ := u.u81_exists_mem_centralizer hsp hfour
  refine u81_dvd_card_centralizer (hBR.trans hR.le) hr (u.r_ne_two hr hrp)
    (hR.isPGroup.to_le hBR) u.prime_p u.p_ne_two hco (mem_centralizer_iff.2 fun β hβ => ?_)
  obtain ⟨x₀, hx₀, x₁, hx₁, c', hc', rfl⟩ := u.u81_omega_decomp hr hrp hR hBR hBel hΩ hβ
  rw [hB0, Subgroup.mem_bot] at hc'
  rw [hc', mul_one]
  exact Commute.mul_left (mem_centralizer_iff.1 hcC x₀ (mem_sup_left hx₀.2))
    (mem_centralizer_iff.1 hcC x₁ (mem_sup_right hx₁.2))

theorem u81_mem_uniqueSet_of_residual (u : U4P D L K n p) {r : ℕ} (hr : r.Prime)
    (hrp : r ∣ 2 ^ p - 1) (hSg : UC6S846.SigmaStd D)
    (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    (h847 : F08.R847 D) (he : 3 < CFSG.Open.evenRank G) (hnsp : ¬ IsStronglyPEmbedded r D.M)
    (hres : ∀ R B : Subgroup G, CFSG.ABGLocalTools.IsSylowOf r R D.M → B ≤ R →
      R ≤ centralizer (B : Set G) → IsElemAbelian r B →
      (∀ x ∈ R, x ^ r = 1 → x ∈ B) → CFSG.Open.pRank r D.M ≤ 3 →
      CFSG.Open.pRank p (centralizer
        ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M))) ≤ 1 →
      barImage D.M B ⊓ centralizer
        ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) ≠ ⊥ →
      ¬ p ∣ Nat.card (centralizer (B : Set G)) → normalizer (B : Set G) ≤ D.M)
    {A : Subgroup G} (hAL : A ≤ L) (hAr : Nat.card A = r) :
    A ∈ uniqueSet D.M := by
  have hns := UC6S846.not_solvable_of_mem_calC u.hL
  have hsp := UC6S846.sp_of_mem_sig hSg hns u.hσ
  have hr2 := u.r_ne_two hr hrp
  haveI : Fact p.Prime := ⟨u.prime_p⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hr3 : CFSG.Open.pRank r D.M ≤ 3 := by
    by_contra h4
    exact hnsp (UC6S846.sp_of_mem_sig hSg hns (hSg.four_mem _ hr hr2 (by omega)))
  have hAp : IsPGroup r A := IsPGroup.of_card (n := 1) (by rw [hAr, pow_one])
  obtain ⟨R, hR, hAR⟩ := PartTwo.exists_isSylowOf_ge_of_isPGroup hAp (hAL.trans u.hL.1.le)
  obtain ⟨B, hBR, hRB, hBel, hΩ⟩ := u.u81_exists_omega hr hrp hr3 hR
  have hAB : A ≤ B := fun x hx => hΩ x (hAR hx) (by
    have h := pow_card_eq_one' (x := (⟨x, hx⟩ : ↥A))
    rw [hAr] at h
    exact congrArg Subtype.val h)
  have hNA : normalizer (A : Set G) ≤ D.M :=
    r847Four_of_r847 D h847 he L u.hL A hAL _ hr hr2 hAr p u.hσ
      (uc22s13a_thin8_of_isL2_or_isSz u.shape)
  by_cases hdvd : p ∣ Nat.card (centralizer (B : Set G))
  · exact u81_mem_uniqueSet_of_dvd hsp hR hBR hBel hΩ hAB hNA hdvd
  have hB0 : barImage D.M B ⊓ centralizer
      ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) ≠ ⊥ := fun h =>
    hdvd (u.u81_dvd_of_inf_eq_bot hr hrp hsp (hfour p u.hσ) hR hBR hBel hΩ h)
  have hC1 : CFSG.Open.pRank p (centralizer
      ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M))) ≤ 1 := by
    by_contra h2
    exact hnsp (u.u81_sp_of_two_le_pRank hr hrp hSg h614 h76 (by omega))
  exact CFSG.LocalAnalysis.AGL81TheoremCD.Section8.mem_uniqueSet_of_normalizer_le_of_omega hR hBR
    hBel hΩ (hres R B hR hBR hRB hBel hΩ hr3 hC1 hB0 hdvd) hAB hNA

theorem u81_normalizer_le (u : U4P D L K n p) {r : ℕ}
    (hr : r.Prime) (hrp : r ∣ 2 ^ p - 1) (hsp : IsStronglyPEmbedded p D.M)
    (hfour : 4 ≤ CFSG.Open.pRank p D.M) (h847 : F08.R847 D) (he : 3 < CFSG.Open.evenRank G)
    (h869 : F08.R869NS5 D) (hGL : GL3Excl.GL3Excl) (hGLR : GL3Excl.GL3ExclR3)
    {R B : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R D.M) (hBR : B ≤ R)
    (hRB : R ≤ centralizer (B : Set G)) (hBel : IsElemAbelian r B)
    (hΩ : ∀ x ∈ R, x ^ r = 1 → x ∈ B) (hr3 : CFSG.Open.pRank r D.M ≤ 3)
    (hC1 : CFSG.Open.pRank p (centralizer
      ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M))) ≤ 1)
    (hB0 : barImage D.M B ⊓ centralizer
      ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) ≠ ⊥)
    (hdvd : ¬ p ∣ Nat.card (centralizer (B : Set G))) :
    normalizer (B : Set G) ≤ D.M := by
  by_contra hNM
  have hn := u.prime_p
  have hn2 := u.p_ne_two
  have hr2 := u.r_ne_two hr hrp
  haveI : Fact p.Prime := ⟨hn⟩
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : NeZero r := ⟨hr.ne_zero⟩
  have hBM : B ≤ D.M := hBR.trans hR.le
  obtain ⟨b, hb⟩ := u.u81_exists_basis hr hrp hr3 hR hBR hBel hΩ hB0
  have hCN : centralizer (B : Set G) ≤ normalizer (B : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hCM : centralizer (B : Set G) ≤ D.M :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 (hb.frame.mem 0))).trans
      ((CFSG.RankThree.PartOne.StrongP.centralizer_singleton_le_normalizer_zpowers _).trans
        (hb.normalizer_zpowers_le u hr hrp hBM h847 he h869 0))
  obtain ⟨y, hyNM, hyo⟩ := u.u81_exists_mem_normalizer hr hrp hsp hfour hR hBR hBel hΩ hC1
  have hY : IsStronglyPEmbedded p
      ((normalizer (B : Set G) ⊓ D.M).subgroupOf (normalizer (B : Set G))) := by
    refine hsp.subgroupOf hNM ?_
    have h := orderOf_dvd_natCard (⟨y, hyNM⟩ : ↥(normalizer (B : Set G) ⊓ D.M))
    rwa [Subgroup.orderOf_mk, hyo] at h
  have hkY : hb.frame.rho.ker ≤
      (normalizer (B : Set G) ⊓ D.M).subgroupOf (normalizer (B : Set G)) := by
    rw [hb.frame.ker_rho]
    exact fun m hm => Subgroup.mem_subgroupOf.2 ⟨m.2, hCM (Subgroup.mem_subgroupOf.1 hm)⟩
  have hpk : ¬ p ∣ Nat.card hb.frame.rho.ker := by
    rwa [hb.frame.ker_rho, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv]
  have hemb := u81_isStronglyPEmbedded_subgroupOf_range hY hb.frame.rho hkY hpk
  have hrH : ¬ r ∣ Nat.card
      (((normalizer (B : Set G) ⊓ D.M).subgroupOf (normalizer (B : Set G))).map
        hb.frame.rho) := by
    rw [← Subgroup.relIndex_ker]
    intro h
    obtain ⟨-, -, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1
      (hR.of_le (le_inf (hRB.trans hCN) hR.le) inf_le_right)
    refine hidx ?_
    rw [← Subgroup.relIndex_subgroupOf
      (inf_le_left : normalizer (B : Set G) ⊓ D.M ≤ normalizer (B : Set G))]
    refine h.trans (Subgroup.relIndex_dvd_of_le_left _ ?_)
    rw [hb.frame.ker_rho]
    exact fun m hm => Subgroup.mem_subgroupOf.2 (hRB (Subgroup.mem_subgroupOf.1 hm))
  have hmemY : ∀ {m : G} (h : m ∈ normalizer (B : Set G) ⊓ D.M),
      hb.frame.rho ⟨m, h.1⟩ ∈
        ((normalizer (B : Set G) ⊓ D.M).subgroupOf (normalizer (B : Set G))).map
          hb.frame.rho :=
    fun h => ⟨⟨_, h.1⟩, Subgroup.mem_subgroupOf.2 h, rfl⟩
  have hstab : ∀ g ∈ hb.frame.rho.range,
      (g : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ Pi.single 0 1 ∈
        Submodule.span (ZMod r) {(Pi.single 0 1 : Fin 3 → ZMod r)} →
      g ∈ ((normalizer (B : Set G) ⊓ D.M).subgroupOf (normalizer (B : Set G))).map
        hb.frame.rho := by
    rintro _ ⟨m, rfl⟩ hm
    have h1 := hb.frame.conj_mem_zpowers_of_mulVec m 0 hm
    have hmN : (m : G) ∈ normalizer (zpowers (b 0) : Set G) :=
      Subgroup.mem_normalizer_fintype fun x hx => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
        rw [← conj_zpow]
        exact zpow_mem h1 k
    exact hmemY ⟨m.2, hb.normalizer_zpowers_le u hr hrp hBM h847 he h869 0 hmN⟩
  obtain ⟨t₁, ht₁, ht₁b⟩ := hb.exists_conj_zero u hr hrp hBM
  obtain ⟨t₂, ht₂, ht₂b⟩ := hb.exists_conj_one u hr hrp hBM
  have hd₁ : (hb.frame.rho ⟨t₁, ht₁.1⟩ : Matrix (Fin 3) (Fin 3) (ZMod r)) =
      Matrix.diagonal ![-1, 1, 1] := by
    rw [hb.frame.rho_eq_diagonal ⟨t₁, ht₁.1⟩ ht₁b]
    congr 1
    funext i
    fin_cases i <;> simp
  have hd₂ : (hb.frame.rho ⟨t₂, ht₂.1⟩ : Matrix (Fin 3) (Fin 3) (ZMod r)) =
      Matrix.diagonal ![1, -1, 1] := by
    rw [hb.frame.rho_eq_diagonal ⟨t₂, ht₂.1⟩ ht₂b]
    congr 1
    funext i
    fin_cases i <;> simp
  have hW : IsIrreducibleMatrixRep hb.frame.rho.range.subtype :=
    hb.frame.isIrreducible hr2 hd₁ hd₂ fun I hI hIu hle =>
      hNM (hle.trans (hb.normalizer_closure_le u hr hrp hBM h847 he h869 hsp hfour hI hIu))
  obtain ⟨α, hα⟩ := hb.frame.exists_rho_eq_diagonal ⟨y, hyNM.1⟩ fun i =>
    hb.conj_mem_zpowers u hBM hyNM.2 hyNM.1 (by rw [hyo]; exact hn.odd_of_ne_two hn2) i
  have hyp : hb.frame.rho ⟨y, hyNM.1⟩ ^ p = 1 := by
    have h1 : (⟨y, hyNM.1⟩ : ↥(normalizer (B : Set G))) ^ p = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      have h := pow_orderOf_eq_one y
      rwa [hyo] at h
    rw [← map_pow, h1, map_one]
  by_cases hns : ∃ i j, α i ≠ α j
  · rcases u.p_eq_five_or_eleven_le with hp5 | hp11
    ·
      have hr31 : r = 31 := by
        have h : r ∣ 31 := by
          rw [hp5] at hrp
          simpa using hrp
        exact (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h
      exact hGL r p (Or.inr ⟨hr31, hp5⟩) hb.frame.rho.range
        (((normalizer (B : Set G) ⊓ D.M).subgroupOf (normalizer (B : Set G))).map hb.frame.rho) hW
        (Subgroup.map_le_range _ _) hemb hrH hstab _ (hmemY ht₁) hd₁ _ (hmemY ht₂) hd₂ _
        (hmemY hyNM) hyp α hα hns
    ·
      exact hGLR r p hn hp11 (PartTwo.s13_seven_le_of_dvd (hn.odd_of_ne_two hn2) hr hrp)
        hb.frame.rho.range
        (((normalizer (B : Set G) ⊓ D.M).subgroupOf (normalizer (B : Set G))).map hb.frame.rho) hW
        (Subgroup.map_le_range _ _) hemb hrH hstab _ (hmemY ht₁) hd₁ _ (hmemY ht₂) hd₂ _
        (hmemY hyNM) hyp α hα hns
  have hsc : ∀ i j, α i = α j := fun i j => by
    by_contra h
    exact hns ⟨i, j, h⟩
  have hcent : ∀ w : GL (Fin 3) (ZMod r),
      w * hb.frame.rho ⟨y, hyNM.1⟩ = hb.frame.rho ⟨y, hyNM.1⟩ * w := by
    intro w
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hα,
      show Matrix.diagonal α = Matrix.scalar (Fin 3) (α 0) by
        rw [Matrix.scalar_apply]
        congr 1
        funext i
        exact hsc i 0]
    exact (Matrix.scalar_commute (α 0) (fun r' => Commute.all _ _) _).eq.symm
  have hρy1 : hb.frame.rho ⟨y, hyNM.1⟩ ≠ 1 := by
    intro h1
    have h := orderOf_dvd_natCard
      (⟨y, (hb.frame.rho_eq_one_iff ⟨y, hyNM.1⟩).1 h1⟩ : ↥(centralizer (B : Set G)))
    rw [Subgroup.orderOf_mk, hyo] at h
    exact hdvd h
  obtain ⟨z, hz⟩ : ∃ z : ↥hb.frame.rho.range, (z : GL (Fin 3) (ZMod r)) =
      hb.frame.rho ⟨y, hyNM.1⟩ := ⟨⟨_, ⟨⟨y, hyNM.1⟩, rfl⟩⟩, rfl⟩
  have hz1 : z ≠ 1 := fun h => hρy1 (by rw [← hz, h, Subgroup.coe_one])
  have hzp : z ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hz, hyp, Subgroup.coe_one])
  have hzY : z ∈ (((normalizer (B : Set G) ⊓ D.M).subgroupOf (normalizer (B : Set G))).map
      hb.frame.rho).subgroupOf hb.frame.rho.range :=
    Subgroup.mem_subgroupOf.2 (by rw [hz]; exact hmemY hyNM)
  have hCz := hemb.centralizer_le hz1 hzp hzY
  refine hNM fun m hm => ?_
  have hw : (⟨hb.frame.rho ⟨m, hm⟩, ⟨⟨m, hm⟩, rfl⟩⟩ : ↥hb.frame.rho.range) ∈
      (((normalizer (B : Set G) ⊓ D.M).subgroupOf (normalizer (B : Set G))).map
        hb.frame.rho).subgroupOf hb.frame.rho.range :=
    hCz (Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hz]
      exact hcent _)))
  obtain ⟨m', hm'Y, hm'⟩ := Subgroup.mem_subgroupOf.1 hw
  have hk : m'⁻¹ * ⟨m, hm⟩ ∈ hb.frame.rho.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hm']
    exact inv_mul_cancel _
  have hmY := Subgroup.mul_mem _ hm'Y (hkY hk)
  rw [mul_inv_cancel_left] at hmY
  exact (Subgroup.mem_subgroupOf.1 hmY).2

end U4P

theorem r8101U3_of_inputs
    {D : Data G} (hSg : UC6S846.SigmaStd D)
    (hfour : 3 < evenRank G → ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (h847 : F08.R847 D)
    (h869 : F08.R869NS5 D) (hGL : GL3Excl.GL3Excl) (hGLR : GL3Excl.GL3ExclR3) :
    R8101U3 D := by
  intro he L n s r p k hL hc2 hL2 hs hsn hr hrs hp hk hn hcong A hAL hAr
  obtain ⟨K, hKne, hset, hKC⟩ := uc22s21ru4e_exists_second_member hc2 hL
  have u : U4P D L K n p := ⟨hL, hKC, hKne, hset, hc2, hL2, hp, ⟨k, hk, hn⟩, hcong⟩
  have hrp : r ∣ 2 ^ p - 1 := by
    have hsp : s ∣ p := by
      rw [hn] at hsn
      exact (Nat.Coprime.pow_right k hs.coprime_two_right).dvd_of_dvd_mul_left hsn
    rcases (Nat.dvd_prime u.prime_p).1 hsp with rfl | rfl
    · have h1 : r ∣ 1 := by simpa using hrs
      exact absurd (Nat.dvd_one.1 h1) hr.one_lt.ne'
    · exact hrs
  haveI : Fact r.Prime := ⟨hr⟩
  by_cases hspr : IsStronglyPEmbedded r D.M
  · refine uc22p22r_mem_uniqueSet_of_sp D hr hspr (hAL.trans hL.1.le)
      (IsPGroup.of_card (n := 1) (by rw [hAr, pow_one])) ?_
    rintro rfl
    rw [Subgroup.card_bot] at hAr
    exact hr.one_lt.ne hAr
  · exact u.u81_mem_uniqueSet_of_residual hr hrp hSg (hfour he) h614 h76 h847 he hspr
      (fun _ _ hR hBR hRB hBel hΩ hr3 hC1 hB0 hdvd =>
        u.u81_normalizer_le hr hrp
          (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hp) (hfour he p hp)
          h847 he h869 hGL hGLR hR hBR hRB hBel hΩ hr3 hC1 hB0 hdvd)
      hAL hAr

end CFSG.LocalAnalysis.UniquenessCase.UC22
