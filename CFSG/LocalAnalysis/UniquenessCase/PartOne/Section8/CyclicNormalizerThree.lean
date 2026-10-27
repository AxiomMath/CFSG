module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.TwoExtraspecialThree
public import CFSG.LocalAnalysis.UniquenessCase.UC6R3
public import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (IsSL3Four R8_108)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem normalizer_sylow_le_of_r6_3 (D : Data G) (h63 : UC6.R6_3 D) {P E : Subgroup G}
    (hPM : P ≤ D.M) (hEP : E ≤ P) (hEel : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 E ≤ D.M) :
    Subgroup.normalizer (P : Set G) ≤ D.M := by
  have hEM : E ≤ D.M := hEP.trans hPM
  have hU' : calMOf E = {D.M} :=
    h63 3 Nat.prime_three (by norm_num) E hEM hEel (by rw [hE9]; norm_num) hΓ
  have hEu : E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := by
    refine CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_forall D.maxLocal hEM ?_
    intro H hH hEH
    have hmem : H ∈ calMOf E := ⟨hH, hEH⟩
    rw [hU'] at hmem
    simpa using hmem
  exact CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal
    (CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hEu hEP hPM)

theorem normalizer_le_of_le_sup_of_card_three (D : Data G) (h69 : UC6.R6_9 D)
    (hsub : D.sig ⊆ D.sig1) {P R R' : Subgroup G} (hPM : P ≤ D.M) (hP3 : IsPGroup 3 P)
    (hT : TwoExtraThree P R R') (hΓR : CFSG.Open.rankThreeGamma 1 3 R ≤ D.M)
    {Y : Subgroup G} (hYQ : Y ≤ R ⊔ R') (hY3 : Nat.card Y = 3) :
    Subgroup.normalizer (Y : Set G) ≤ D.M := by
  classical
  have hQM : R ⊔ R' ≤ D.M := hT.le.trans hPM
  have hQp : IsPGroup 3 ↥(R ⊔ R') := hP3.to_le hT.le
  have hYne : Y ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hY3
    omega
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hYne
  have hyord : orderOf (y : G) = 3 := by
    have hdvd : orderOf (y : G) ∣ 3 := by
      rw [← hY3, Subgroup.orderOf_coe]
      exact orderOf_dvd_natCard y
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (Subtype.ext (orderOf_eq_one_iff.mp h)) hy1
    · exact h
  have hYeq : Y = Subgroup.zpowers (y : G) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr y.2) ?_).symm
    rw [Nat.card_zpowers, hyord, hY3]
  obtain ⟨r, hr, r', hr', hrr'⟩ :=
    CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_commute hT.comm (hYQ y.2)
  obtain ⟨E, hrE, hER, hEel, hE9⟩ :=
    exists_elemAbelian_nine_of_isExtraspecial_of_pow_three hT.extra hT.exp hr
  have hEC : E ≤ Subgroup.centralizer (Y : Set G) := by
    intro e he
    rw [hYeq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_iff]
    rintro _ rfl
    have h1 : e * r = r * e :=
      congrArg Subtype.val (hEel.1.is_comm.comm ⟨e, he⟩ ⟨r, hrE⟩)
    have h2 : e * r' = r' * e := hT.comm e (hER he) r' hr'
    rw [hrr']
    calc r * r' * e = r * (r' * e) := by group
      _ = r * (e * r') := by rw [h2]
      _ = (r * e) * r' := by group
      _ = (e * r) * r' := by rw [h1]
      _ = e * (r * r') := by group
  by_contra hN
  have hEM : E ≤ D.M := hER.trans (le_sup_left.trans hQM)
  have hΓE : CFSG.Open.rankThreeGamma 1 3 E ≤ D.M :=
    (CFSG.HardMathSupport.Solomon.Proving.GLBCore_mono (p := 3) (k := 1) hER).trans hΓR
  have hEN : E ≤ Subgroup.normalizer (Y : Set G) :=
    hEC.trans (Subgroup.centralizer_le_normalizer (Y : Set G))
  have hstep := h69 hsub 3 Nat.prime_three (by norm_num) E hEM hEel (by rw [hE9]; norm_num)
    hΓE 3 Y Nat.prime_three (hYQ.trans hQM) hY3 hEN hN (R ⊔ R') hQM hQp hYQ
  have hcomm69 := hstep.2.1
  rw [hT.upperCentralSeries_two_map] at hcomm69
  have hYZ : Y ≤ R ⊓ R' := by
    rw [← hT.center_map]
    intro x hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hYQ hx⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    exact (hcomm69 q q.2 x hx).symm
  have hYel : CFSG.Open.IsElemAbelian 3 Y := by
    refine ⟨(isCyclic_of_card_dvd_prime (p := 3) (by rw [hY3])).isMulCommutative, ?_⟩
    intro x hx
    have h := pow_card_eq_one' (G := ↥Y) (x := ⟨x, hx⟩)
    simpa [hY3] using congrArg Subtype.val h
  have hYrank : 1 ≤ CFSG.Open.pRank 3 Y :=
    CFSG.SectionRank.le_pRank (p := 3) (k := 1) (by norm_num) le_rfl hYel
      (by rw [hY3]; norm_num)
  exact hN ((CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore
    (hYZ.trans inf_le_left) hYrank).trans hΓR)

theorem mem_of_map_conj_le {M P Z Q : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P M)
    (hPZ : P ≤ Subgroup.centralizer (Z : Set G)) (hNP : Subgroup.normalizer (P : Set G) ≤ M)
    (hY : ∀ Y : Subgroup G, Y ≤ Q → Nat.card Y = 3 → Subgroup.normalizer (Y : Set G) ≤ M)
    (hZ3 : Nat.card Z = 3) {g : G} (hg : Z.map (MulAut.conj g).toMonoidHom ≤ Q) : g ∈ M := by
  classical
  set Y : Subgroup G := Z.map (MulAut.conj g).toMonoidHom with hYdef
  have hY3' : Nat.card Y = 3 := by
    rw [hYdef, Subgroup.card_map_of_injective (MulAut.conj g).injective, hZ3]
  have hCY : Subgroup.centralizer (Y : Set G) ≤ M :=
    (Subgroup.centralizer_le_normalizer (Y : Set G)).trans (hY Y hg hY3')
  have hPgM : P.map (MulAut.conj g).toMonoidHom ≤ M := by
    refine le_trans ?_ hCY
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    have hxz : z * x = x * z := Subgroup.mem_centralizer_iff.mp (hPZ hx) z hz
    change (MulAut.conj g) z * (MulAut.conj g) x = (MulAut.conj g) x * (MulAut.conj g) z
    rw [← map_mul, ← map_mul, hxz]
  have hPgSyl : CFSG.ABGLocalTools.IsSylowOf 3 (P.map (MulAut.conj g).toMonoidHom) M := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hPgM ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hP.card_eq
  obtain ⟨m, hmM, hm⟩ := hP.exists_mem_conj hPgSyl
  have hle : P.map (MulAut.conj (m⁻¹ * g)).toMonoidHom ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : g * y * g⁻¹ ∈ P.map (MulAut.conj g).toMonoidHom := ⟨y, hy, rfl⟩
    have h2 := (hm _).mp h1
    have heq : (MulAut.conj (m⁻¹ * g)).toMonoidHom y = m⁻¹ * (g * y * g⁻¹) * m := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [heq]
    exact h2
  have heqP : P.map (MulAut.conj (m⁻¹ * g)).toMonoidHom = P :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj (m⁻¹ * g)).injective])
  have hn : m⁻¹ * g ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr heqP
  have hgm : g = m * (m⁻¹ * g) := by group
  rw [hgm]
  exact M.mul_mem hmM (hNP hn)

theorem rankThreeGamma_le_of_inf_le {M P R R' : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P M) (hT : TwoExtraThree P R R')
    (hNP : Subgroup.normalizer (P : Set G) ≤ M)
    (hY : ∀ Y : Subgroup G, Y ≤ R ⊔ R' → Nat.card Y = 3 → Subgroup.normalizer (Y : Set G) ≤ M)
    {E : Subgroup G} (hZE : R ⊓ R' ≤ E) (hEQ : E ≤ R ⊔ R') (hEel : CFSG.Open.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) : CFSG.Open.rankThreeGamma 1 3 E ≤ M := by
  classical
  refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall (p := 3) (k := 1) ?_
  intro F hFE hF
  have hFne : F ≠ ⊥ := by
    intro hbot
    rw [hbot] at hF
    obtain ⟨B, hB, -, hBcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
      (⊥ : Subgroup G)
    have h1 : B = ⊥ := le_bot_iff.mp hB
    rw [h1, Subgroup.card_bot] at hBcard
    have : (3 : ℕ) ^ CFSG.Open.pRank 3 (⊥ : Subgroup G) ≥ 3 ^ 1 :=
      Nat.pow_le_pow_right (by norm_num) hF
    omega
  have hdvd : Nat.card F ∣ 9 := hE9 ▸ Subgroup.card_dvd_of_le hFE
  have hcases : Nat.card F = 3 ∨ Nat.card F = 9 := by
    have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [h9] at hdvd
    obtain ⟨k, hk, hFk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases k
    · exact absurd (Subgroup.eq_bot_of_card_eq F (by simpa using hFk)) hFne
    · left; simpa using hFk
    · right; simpa using hFk
  rcases hcases with h3 | h9
  · exact hY F (hFE.trans hEQ) h3
  · have hFE' : F = E := Subgroup.eq_of_le_of_card_ge hFE (by rw [hE9, h9])
    subst hFE'
    intro g hg
    refine mem_of_map_conj_le hP (hT.le_centralizer_inf hP.isPGroup) hNP hY hT.card_inf ?_
    have hgF : F.map (MulAut.conj g).toMonoidHom = F :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    calc (R ⊓ R').map (MulAut.conj g).toMonoidHom ≤ F.map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono hZE
      _ = F := hgF
      _ ≤ R ⊔ R' := hEQ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
