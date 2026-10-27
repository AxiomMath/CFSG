module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsSevenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneSixTen
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qs
public import CFSG.GroupTheory.SLTwoInvertsElemAbelian
public import CFSG.GroupTheory.SylowNormalElements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC6 Subgroup
open scoped Pointwise MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem mem_M_of_inverting {M : Subgroup G} {q : ℕ} (hq : q.Prime) {Q A : Subgroup G}
    (hQexp : ∀ x ∈ Q, x ^ q = 1) (hΓ : rankThreeGamma 1 q Q ≤ M) {a : G} (haM : a ∈ M)
    (hAleQa : A ≤ uniqueFourConj a Q) (hAne : A ≠ ⊥) {t : G}
    (htinv : ∀ x ∈ A, t * x * t⁻¹ = x⁻¹) : t ∈ M := by
  have htA : t ∈ normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      change t * x * t⁻¹ ∈ A
      rw [htinv x hx]
      exact A.inv_mem hx
    · intro x hx
      refine ⟨x⁻¹, A.inv_mem hx, ?_⟩
      change t * x⁻¹ * t⁻¹ = x
      rw [htinv x⁻¹ (A.inv_mem hx), inv_inv]
  let A' : Subgroup G := uniqueFourConj a⁻¹ A
  have hA'Q : A' ≤ Q := by
    have h := uniqueFourConj_mono hAleQa a⁻¹
    rwa [uniqueFourConj_inv_conj] at h
  have hNA' : normalizer (A' : Set G) ≤ M :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSeven.normalizer_le_of_gamma_le hq hQexp
      hΓ hA'Q (uniqueFourConj_ne_bot hAne a⁻¹)
  have hNA : normalizer (A : Set G) ≤ M := by
    have h1 := uniqueFourConj_mono hNA' a
    have h2 : uniqueFourConj a (normalizer (A' : Set G)) = normalizer (A : Set G) := by
      rw [uniqueFourConj_normalizer A' a]
      have hA'eq : uniqueFourConj a A' = A := by
        show uniqueFourConj a (uniqueFourConj a⁻¹ A) = A
        exact uniqueFourConj_conj_inv
      rw [hA'eq]
    have h3 : uniqueFourConj a M = M :=
      uniqueFourConj_eq_self_iff.mpr (Subgroup.le_normalizer haM)
    calc normalizer (A : Set G) = uniqueFourConj a (normalizer (A' : Set G)) := h2.symm
      _ ≤ uniqueFourConj a M := h1
      _ = M := h3
  exact hNA htA

private theorem E_le_centralizer_of_inverting (D : Data G) (hUZ : D.U = D.Z)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Subgroup G} (hEM : E ≤ D.M)
    (hEel : IsElemAbelian q E) {t : G} (htM : t ∈ D.M) {k : ℕ} (htk : orderOf t = 2 ^ k)
    (htinv : ∀ x ∈ E, t * x * t⁻¹ = x⁻¹) :
    E ≤ Subgroup.centralizer (D.Z : Set G) := by
  classical
  have hVZ : InCalV D.M D.Z := hUZ ▸ uc22p22e_inCalV_U D
  have hZleM : D.Z ≤ D.M := hVZ.2.1
  have hMnormZ : D.M ≤ normalizer (D.Z : Set G) := hVZ.2.2.1
  have hZsubN : (D.Z.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZleM).2 hMnormZ
  let C : Subgroup G := D.M ⊓ Subgroup.centralizer (D.Z : Set G)
  have hCeq : C.subgroupOf D.M =
      Subgroup.centralizer (D.Z.subgroupOf D.M : Set ↥D.M) := by
    ext m
    constructor
    · intro hm
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hcin : (m : G) ∈ D.M ⊓ Subgroup.centralizer (D.Z : Set G) :=
        Subgroup.mem_subgroupOf.mp hm
      have hc : (m : G) ∈ Subgroup.centralizer (D.Z : Set G) :=
        (Subgroup.mem_inf.mp hcin).2
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hc) (z : G) hz)
    · intro hm
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨m.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact congrArg Subtype.val
        ((Subgroup.mem_centralizer_iff.mp hm) ⟨z, hZleM hz⟩ (Subgroup.mem_subgroupOf.mpr hz))
  haveI : (D.Z.subgroupOf D.M).Normal := hZsubN
  have hCnorm : (C.subgroupOf D.M).Normal := by
    rw [hCeq]
    exact Subgroup.normal_centralizer
  have hTleC : D.T ≤ C := by
    change D.T ≤ D.M ⊓ Subgroup.centralizer (D.Z : Set G)
    refine le_inf D.sylowM.le ?_
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hz).2.1 t ht).symm
  have hC_le : C ≤ D.M := inf_le_left
  have htC : t ∈ C :=
    CFSG.GroupTheory.mem_of_normal_of_isSylowOf (M := D.M) (K := C) (P := D.T)
      hCnorm D.sylowM hTleC htM htk
  intro x hxE
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hxM : x ∈ D.M := hEM hxE
  let y : G := x ^ ((q - 1) / 2)
  have hyE : y ∈ E := E.pow_mem hxE _
  have hyM : y ∈ D.M := hEM hyE
  have hty : t * y * t⁻¹ = y⁻¹ := htinv y hyE
  have hxq : x ^ q = 1 := hEel.2 x hxE
  obtain ⟨j, hj⟩ := hq.odd_of_ne_two hq2
  have hq1 : q - 1 = 2 * j := by omega
  have hdiv : (q - 1) / 2 = j := by omega
  have hpow : x ^ (q - 1) = x⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ q), hxq]
  have hy2 : y ^ 2 = x⁻¹ := by
    rw [show y = x ^ j by simp [y, hdiv], ← pow_mul, show j * 2 = 2 * j by ring, ← hq1]
    exact hpow
  have hxeq : x = t * (y * t⁻¹ * y⁻¹) := by
    have h1 : t * (y * t⁻¹ * y⁻¹) = (t * y * t⁻¹) * y⁻¹ := by group
    rw [h1, hty]
    have h2 : y⁻¹ * y⁻¹ = (y ^ 2)⁻¹ := by group
    rw [h2, hy2, inv_inv]
  have hyty : y * t⁻¹ * y⁻¹ ∈ C := by
    have ht'in : t⁻¹ ∈ C := C.inv_mem htC
    have h := hCnorm.conj_mem ⟨t⁻¹, hC_le ht'in⟩ (Subgroup.mem_subgroupOf.mpr ht'in)
      ⟨y, hyM⟩
    simpa using Subgroup.mem_subgroupOf.mp h
  have hxC : x ∈ C := hxeq ▸ C.mul_mem htC hyty
  have hxC' : x ∈ D.M ⊓ Subgroup.centralizer (D.Z : Set G) := hxC
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxC').2) z hz

private theorem normalizer_le_uniqueFourConj {M : Subgroup G} {q : ℕ} (hq : q.Prime)
    {Q B : Subgroup G} (hQexp : ∀ x ∈ Q, x ^ q = 1) (hΓ : rankThreeGamma 1 q Q ≤ M)
    {b g' : G} (hbM : b ∈ M) (hBleQbg : B ≤ uniqueFourConj (b * g') Q) (hBne : B ≠ ⊥) :
    normalizer (B : Set G) ≤ uniqueFourConj g' M := by
  have hB'Q : uniqueFourConj (b * g')⁻¹ B ≤ Q := by
    have h := uniqueFourConj_mono hBleQbg (b * g')⁻¹
    rwa [uniqueFourConj_inv_conj] at h
  have hNB' : normalizer (uniqueFourConj (b * g')⁻¹ B : Set G) ≤ M :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSeven.normalizer_le_of_gamma_le hq hQexp
      hΓ hB'Q (uniqueFourConj_ne_bot hBne (b * g')⁻¹)
  have hNB : normalizer (B : Set G) ≤ uniqueFourConj g' M := by
    have h1 := uniqueFourConj_mono hNB' (b * g')
    have h2 : uniqueFourConj (b * g')
          (normalizer (uniqueFourConj (b * g')⁻¹ B : Set G)) = normalizer (B : Set G) := by
      rw [uniqueFourConj_normalizer (uniqueFourConj (b * g')⁻¹ B) (b * g'),
        uniqueFourConj_conj_inv]
    have hcomp : uniqueFourConj (b * g') M = uniqueFourConj g' (uniqueFourConj b M) := by
      unfold uniqueFourConj
      rw [mul_inv_rev, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have h3 : uniqueFourConj (b * g') M = uniqueFourConj g' M := by
      rw [hcomp, uniqueFourConj_eq_self_iff.mpr (Subgroup.le_normalizer hbM)]
    calc normalizer (B : Set G) =
          uniqueFourConj (b * g') (normalizer (uniqueFourConj (b * g')⁻¹ B : Set G)) := h2.symm
      _ ≤ uniqueFourConj (b * g') M := h1
      _ = uniqueFourConj g' M := h3
  exact hNB

theorem inf_map_conj_eq_bot_of_gamma_le (D : Data G) (h63 : UC6.R6_3 D) (hUZ : D.U = D.Z)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Q R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf q R D.M) (hQR : Q ≤ R)
    (hQRn : (Q.subgroupOf R).Normal) (hQnc : ¬ IsCyclic ↥Q)
    (hQexp : ∀ x ∈ Q, x ^ q = 1) (hΓ : rankThreeGamma 1 q Q ≤ D.M) {g : G}
    (hg : g ∉ D.M) : Q ⊓ D.M.map (MulAut.conj g).toMonoidHom = ⊥ := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hQq : IsPGroup q Q := hR.isPGroup.to_le hQR
  set g' : G := g⁻¹ with hg'def
  have hg' : g' ∉ D.M := by
    intro h
    exact hg (by simpa [hg'def] using D.M.inv_mem h)
  obtain ⟨E₀, hE₀Q, hE₀el, hE₀card⟩ :=
    CFSG.Quasithin.A1c.exists_isElemAbelian_card_sq hq2 hQq hQnc
  have hE₀M : E₀ ≤ D.M := (hE₀Q.trans hQR).trans hR.le
  have hΓE₀ : rankThreeGamma 1 q E₀ ≤ D.M :=
    (CFSG.HardMathSupport.Solomon.Proving.GLBCore_mono (p := q) (k := 1) hE₀Q).trans hΓ
  have hEU : UniqueMax D.M E₀ := h63 q hq hq2 E₀ hE₀M hE₀el hE₀card hΓE₀
  have hNR : normalizer (R : Set G) ≤ D.M :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSeven.normalizer_le_of_uniqueMax_le D hEU
      (hE₀Q.trans hQR) hR.le
  have hRtop : CFSG.ABGLocalTools.IsSylowOf q R ⊤ :=
    uc22p22q_isSylowOf_top_of_normalizer hR hNR
  have hRidx : ¬ q ∣ R.index := by
    have h := (CFSG.ABGLocalTools.isSylowOf_iff.1 hRtop).2.2
    rwa [Subgroup.relIndex_top_right] at h
  let P : Sylow q G := hR.isPGroup.toSylow hRidx
  have hPcoe : (P : Subgroup G) = R := IsPGroup.toSylow_coe _ _
  have hQleP : Q ≤ (P : Subgroup G) := by rw [hPcoe]; exact hQR
  have hQnormP : (Q.subgroupOf (P : Subgroup G)).Normal := by rw [hPcoe]; exact hQRn
  by_contra hne
  let X : Subgroup G := Q ⊓ D.M.map (MulAut.conj g).toMonoidHom
  have hXne : X ≠ ⊥ := fun h => hne h
  have hXeq : X = Q ⊓ uniqueFourConj g' D.M := by
    simp [X, uniqueFourConj, g']
  have hXM : X ≤ D.M := by
    intro x hx
    have hx' : x ∈ Q ⊓ D.M.map (MulAut.conj g).toMonoidHom := hx
    exact hQR.trans hR.le (Subgroup.mem_inf.mp hx').1
  have hXQ : X ≤ Q := by
    intro x hx
    have hx' : x ∈ Q ⊓ D.M.map (MulAut.conj g).toMonoidHom := hx
    exact (Subgroup.mem_inf.mp hx').1
  have hXp : IsPGroup q X := hQq.to_le hXQ
  have hNX : normalizer (X : Set G) ≤ D.M :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSeven.normalizer_le_of_gamma_le hq hQexp
      hΓ hXQ hXne
  have hXMg : X ≤ uniqueFourConj g' D.M := by rw [hXeq]; exact inf_le_right
  have h610 := CFSG.LocalAnalysis.UniquenessCase.PartTwo.r6_10_of_r6_3 D h63 q hq hq2 P Q
    hQleP hQnormP hQnc hQexp hΓ X hXM hXp hNX g' hg' hXMg
  obtain ⟨⟨a, haM, b, hbM, A, B, E, hAcard, hBcard, hAleQa, hBleQbg, hEel, hEcard, hAB,
    hEeq, φ, hφsurj, hφker⟩, h610_3⟩ := h610
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hAcard
    exact hq.ne_one hAcard.symm
  have hBne : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hBcard
    exact hq.ne_one hBcard.symm
  have hAleE : A ≤ E := hAB ▸ le_sup_left
  have hBleE : B ≤ E := hAB ▸ le_sup_right
  have hQaM : uniqueFourConj a Q ≤ D.M := by
    rintro _ ⟨y, hy, rfl⟩
    change a⁻¹ * y * (a⁻¹)⁻¹ ∈ D.M
    exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem haM) ((hQR.trans hR.le) hy))
      (by simpa using haM)
  have hEM : E ≤ D.M := by
    rw [hEeq]
    exact sup_le (inf_le_left.trans hQaM) inf_le_right
  have hHE : (uniqueFourConj a Q ⊓ normalizer (E : Set G)) ⊔
      (uniqueFourConj (b * g') Q ⊓ normalizer (E : Set G)) ≤ normalizer (E : Set G) :=
    sup_le inf_le_right inf_le_right
  obtain ⟨t, -, ⟨k, htk⟩, htinv⟩ :=
    CFSG.GroupTheory.exists_two_element_inverting_of_sl2_quotient hq2 hEel hEcard hHE φ
      hφsurj hφker
  have htM : t ∈ D.M :=
    mem_M_of_inverting (M := D.M) hq hQexp hΓ haM hAleQa hAne
      (fun x hx => htinv x (hAleE hx))
  have hEC : E ≤ Subgroup.centralizer (D.Z : Set G) :=
    E_le_centralizer_of_inverting D hUZ hq hq2 hEM hEel htM htk htinv
  have hBleCZ : B ≤ Subgroup.centralizer (D.Z : Set G) := hBleE.trans hEC
  have hZleCB : D.Z ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.le_centralizer_iff.mpr hBleCZ
  have hZleNB : D.Z ≤ normalizer (B : Set G) :=
    hZleCB.trans (Subgroup.centralizer_le_normalizer (B : Set G))
  have hNB : normalizer (B : Set G) ≤ uniqueFourConj g' D.M :=
    normalizer_le_uniqueFourConj (M := D.M) hq hQexp hΓ hbM hBleQbg hBne
  have hZle : D.Z ≤ uniqueFourConj g' D.M := hZleNB.trans hNB
  exact h610_3 D.Z (hUZ ▸ uc22p22e_inCalV_U D) hZle

theorem s23_7_1_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h77 : F07.R77Eq D)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) (h6 : S23_6 D Ch)
    (hrk : ∀ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M) (h63 : UC6.R6_3 D) : S23_7_1 D Ch := by
  intro h1930 c q hq hq2 Q hQM hQq hQnc hQexp hQcl p hp P hPM hPn hPO Q0 hQ0 hQN hQn g hg
  haveI : Fact q.Prime := ⟨hq⟩
  have hUZ : D.U = D.Z := (h4 h1930 c).1
  have hσ : D.sig ⊆ D.sig1 := fun r hr => (h6 h1930 c) ▸ hr
  have hspSig : ∀ r ∈ D.sig, CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M := by
    intro r hr
    exact hsp r ((h6 h1930 c) ▸ hr)
  have hΓ : rankThreeGamma 1 q Q ≤ D.M :=
    gamma_le_of_s23_7 D h77 hσ hspSig hrk hq hq2 hQM hQq hQnc hQexp hQcl hp hPM hPn hPO
      hQ0 hQN hQn
  obtain ⟨R, hR, hQR, hQRn⟩ :=
    CFSG.GroupTheory.exists_isSylowOf_le_of_normal_of_le_normalizer hPM hPn hQq hQ0 hQN hQn
  exact inf_map_conj_eq_bot_of_gamma_le D h63 hUZ hq hq2 hR hQR hQRn hQnc hQexp hΓ hg

theorem s23_7_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h77 : F07.R77Eq D)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) (h6 : S23_6 D Ch)
    (hrk : ∀ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M) (h63 : UC6.R6_3 D) (h211 : S21_1 D Ch) :
    S23_7 D Ch :=
  ⟨s23_7_1_of D Ch h4 h77 hsp h6 hrk h63,
    s23_7_2_of D Ch (s23_7_1_of D Ch h4 h77 hsp h6 hrk h63) h77 hsp h6 hrk h63 h211⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
