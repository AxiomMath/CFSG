module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.OmegaMinusStructure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.OmegaMinusQ
public import CFSG.GroupTheory.PRankTwoOfPGroup
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9Group
public import CFSG.GroupTheory.CoprimeActionSupport.CentralizerKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem normalizer_le_normalizer_zOneOf (T : Subgroup G) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (zOneOf T : Set G) := by
  simpa [zOneOf, CFSG.inSubgroup] using
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.normalizer_le_normalizer_higherElemThompsonOmega
      T 1

private theorem le_zOneOf_of_le_center {T A : Subgroup G}
    (hA : A ≤ zJOneOf T) (hexp : ∀ x ∈ A, x ^ 2 = 1) : A ≤ zOneOf T := by
  intro x hx
  rw [zJOneOf] at hA
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hA hx)
  rw [Subgroup.mem_map] at hy
  obtain ⟨w, hw, hwy⟩ := hy
  have hy2 : (y : ↥T) ^ 2 = 1 := by
    have hx2 : x ^ 2 = 1 := hexp x hx
    rw [← hyx] at hx2
    exact Subtype.ext (by simpa using hx2)
  have hyK : y ∈ CFSG.higherElemThompsonOmega ↥T 1 := by
    show y ∈ CFSG.omegaOneCenter (CFSG.higherElemThompson ↥T 1)
    exact ⟨Subgroup.mem_map.mpr ⟨w, hw, hwy⟩, hy2⟩
  rw [zOneOf]
  rw [CFSG.inSubgroup]
  exact Subgroup.mem_map.mpr ⟨y, hyK, hyx⟩

private theorem T_le_normalizer_jOf (D : Data G) :
    D.T ≤ Subgroup.normalizer (F12.jOf D.T : Set G) := by
  rw [F12.jOf]
  rw [CFSG.inSubgroup]
  simpa [← CFSG.higherElemThompson_zero] using
    (Subgroup.le_normalizer.trans
      (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.normalizer_le_normalizer_higherElemThompson
        D.T 0))

private theorem T_le_normalizer_zOneOf (D : Data G) :
    D.T ≤ Subgroup.normalizer (zOneOf D.T : Set G) :=
  (Subgroup.le_normalizer.trans (normalizer_le_normalizer_zOneOf D.T))

private theorem jOf_eq_thompsonJ (T : Subgroup G) :
    F12.jOf T = CFSG.Quasithin.thompsonJ T := by
  rw [F12.jOf, CFSG.inSubgroup,
    CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ]

private theorem jOf_le_self (T : Subgroup G) : F12.jOf T ≤ T := by
  rw [jOf_eq_thompsonJ]
  exact CFSG.Quasithin.thompsonJ_le_self T

private theorem jOf_eq_of_le {S T : Subgroup G} (hJ : F12.jOf S ≤ T) (hTS : T ≤ S) :
    F12.jOf T = F12.jOf S := by
  rw [jOf_eq_thompsonJ] at hJ ⊢
  rw [jOf_eq_thompsonJ]
  exact (CFSG.Quasithin.thompsonJ_eq_of_le (S := S) (R := T) hJ hTS).symm

private theorem jOf_le_jOneOf (T : Subgroup G) (hm : 1 < CFSG.pRank 2 ↥T) :
    F12.jOf T ≤ jOneOf T := by
  have hJeq : F12.jOf T = (CFSG.higherElemThompson ↥T 0).map T.subtype := by
    rw [F12.jOf, CFSG.inSubgroup, ← CFSG.higherElemThompson_zero]
  rw [hJeq, jOneOf, CFSG.inSubgroup]
  refine Subgroup.map_mono ?_
  rw [CFSG.higherElemThompson]
  refine sSup_le fun A hA => ?_
  have hAfam := (CFSG.mem_higherElemThompsonFamily_iff 0 A).mp hA
  haveI : CFSG.IsElementaryAbelian 2 ↥A := hAfam.1
  have hrankA : CFSG.pRank 2 ↥A = CFSG.pRank 2 ↥T := by
    rw [CFSG.pRank_eq_of_card_eq_pow (p := 2) one_lt_two hAfam.2, Nat.sub_zero]
  exact CFSG.Quasithin.SteinbergBK.le_higherElemThompson_of_le_pRank hm hAfam.1
    (by rw [hrankA]; exact Nat.sub_le _ _)

private theorem le_centralizer_omegaOneCenter {S : Type} [Group S] (J : Subgroup S) :
    J ≤ Subgroup.centralizer (CFSG.omegaOneCenter J : Set S) := by
  intro j hj z hz
  obtain ⟨⟨w, hw, hwz⟩, -⟩ := hz
  rw [← hwz]
  exact congrArg J.subtype (Subgroup.mem_center_iff.mp hw ⟨j, hj⟩).symm

private theorem jOneOf_le_centralizer_zOneOf (T : Subgroup G) :
    jOneOf T ≤ Subgroup.centralizer (zOneOf T : Set G) := by
  intro x hx
  rw [jOneOf, CFSG.inSubgroup] at hx
  obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [zOneOf, CFSG.inSubgroup] at hz
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  have hc := le_centralizer_omegaOneCenter (CFSG.higherElemThompson ↥T 1) hx'
  have hz'' : z' ∈ CFSG.omegaOneCenter (CFSG.higherElemThompson ↥T 1) := hz'
  exact congrArg T.subtype ((Subgroup.mem_centralizer_iff.mp hc) z' hz'')

private theorem caseB_dedekind (D : Data G) {Q : Subgroup G}
    (hTNJ : D.T ≤ Subgroup.normalizer (F12.jOf D.T : Set G))
    (hQNJ : Q ⊓ Subgroup.normalizer (F12.jOf D.T : Set G) = ⊥)
    (hTQ : Permutes D.T Q) :
    (Q ⊔ D.T) ⊓ Subgroup.normalizer (F12.jOf D.T : Set G) = D.T := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxQ, hxN⟩ := Subgroup.mem_inf.mp hx
    have hset : ((Q ⊔ D.T : Subgroup G) : Set G) = (Q : Set G) * (D.T : Set G) :=
      CFSG.Quasithin.H23P4.coe_sup_eq_mul_of_mul_comm hTQ.symm
    change x ∈ ((Q ⊔ D.T : Subgroup G) : Set G) at hxQ
    rw [hset] at hxQ
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hxQ
    have hbN : b ∈ Subgroup.normalizer (F12.jOf D.T : Set G) := hTNJ hb
    have haN : a ∈ Subgroup.normalizer (F12.jOf D.T : Set G) := by
      have : a = (a * b) * b⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ hbN)
    have habot : a ∈ (⊥ : Subgroup G) := by
      rw [← hQNJ]
      exact Subgroup.mem_inf.mpr ⟨ha, haN⟩
    have ha1 : a = 1 := Subgroup.mem_bot.mp habot
    rw [ha1, one_mul]
    exact hb
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right hx, hTNJ hx⟩

private theorem caseB_frattini_sup {X K T : Subgroup G}
    (hKX : K ≤ X) (hKN : X ≤ Subgroup.normalizer (K : Set G))
    (hP₀ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K) K)
    (hNP : X ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ T) :
    X ≤ K ⊔ T := by
  intro x hx
  have hKmap : K.map (MulAut.conj x).toMonoidHom = K :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hKN hx)
  have hPx : CFSG.ABGLocalTools.IsSylowOf 2
      ((T ⊓ K).map (MulAut.conj x).toMonoidHom) K := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hP₀ ⊢
    obtain ⟨hPle, hP2, hPidx⟩ := hP₀
    refine ⟨(Subgroup.map_mono hPle).trans_eq hKmap, hP2.map _, ?_⟩
    have hidx : ((T ⊓ K).map (MulAut.conj x).toMonoidHom).relIndex
        (K.map (MulAut.conj x).toMonoidHom) = (T ⊓ K).relIndex K :=
      Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj x).toMonoidHom)
        (T ⊓ K) K (MulAut.conj x).injective
    rw [hKmap] at hidx
    rwa [hidx]
  obtain ⟨k, hkK, hconj⟩ := hP₀.exists_mem_conj hPx
  have hnx : k⁻¹ * x ∈ X := X.mul_mem (X.inv_mem (hKX hkK)) hx
  have hnorm : k⁻¹ * x ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hmem : x * y * x⁻¹ ∈ (T ⊓ K).map (MulAut.conj x).toMonoidHom ↔ y ∈ T ⊓ K := by
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
      rw [show x⁻¹ * (x * y * x⁻¹) * x = y by group]
    have h1 := hconj (x * y * x⁻¹)
    rw [hmem] at h1
    calc y ∈ T ⊓ K ↔ k⁻¹ * (x * y * x⁻¹) * k ∈ T ⊓ K := h1
      _ ↔ (k⁻¹ * x) * y * (k⁻¹ * x)⁻¹ ∈ T ⊓ K := by
          constructor <;> intro h <;> convert h using 1 <;> group
  have ht : k⁻¹ * x ∈ T := hNP (Subgroup.mem_inf.mpr ⟨hnx, hnorm⟩)
  have hx' : x = k * (k⁻¹ * x) := by group
  rw [hx']
  exact Subgroup.mul_mem_sup hkK ht

private theorem caseB_quotient_two_of_sup {X K T : Subgroup G}
    (hKX : K ≤ X) (hTK : T ≤ X) (hKN : (K.subgroupOf X).Normal)
    (hX : X ≤ K ⊔ T) (hT2 : IsPGroup 2 ↥T) :
    IsPGroup 2 (↥X ⧸ (K.subgroupOf X)) := by
  classical
  let KX : Subgroup ↥X := K.subgroupOf X
  let TX : Subgroup ↥X := T.subgroupOf X
  have hTX2 : IsPGroup 2 TX := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm
  have hsup : KX ⊔ TX = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKX hTK, Subgroup.subgroupOf_eq_top]
    exact hX
  haveI : KX.Normal := hKN
  haveI : (KX.subgroupOf ⊤).Normal := hKN.subgroupOf ⊤
  have hTXnorm : TX ≤ Subgroup.normalizer (KX : Set ↥X) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hquotTop : IsPGroup 2 ((⊤ : Subgroup ↥X) ⧸ (KX.subgroupOf ⊤)) :=
    CFSG.Quasithin.F112R.isPGroup_quotient_of_sup_eq hTX2 le_top hTXnorm hsup
  have he : (KX.subgroupOf ⊤).map (Subgroup.topEquiv (G := ↥X)).toMonoidHom = KX := by
    ext x
    simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  exact IsPGroup.of_equiv hquotTop
    (QuotientGroup.congr (KX.subgroupOf ⊤) KX (Subgroup.topEquiv (G := ↥X)) he)

private theorem caseB_qGroup_le_of_sup_two {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {X K T Q : Subgroup G} (hKX : K ≤ X) (hTK : T ≤ X)
    (hKN : (K.subgroupOf X).Normal) (hX : X ≤ K ⊔ T) (hT2 : IsPGroup 2 ↥T)
    (hQq : IsPGroup q ↥Q) (hQX : Q ≤ X) :
    Q ≤ K := by
  classical
  let KX : Subgroup ↥X := K.subgroupOf X
  let QX : Subgroup ↥X := Q.subgroupOf X
  let π : ↥X →* (↥X ⧸ KX) := QuotientGroup.mk' KX
  have hquot2 : IsPGroup 2 (↥X ⧸ KX) := caseB_quotient_two_of_sup hKX hTK hKN hX hT2
  have hQXq : IsPGroup q QX := hQq.of_equiv (Subgroup.subgroupOfEquivOfLe hQX).symm
  haveI : Fact q.Prime := ⟨hq⟩
  have hImg2 : IsPGroup 2 (QX.map π) := hquot2.to_subgroup (QX.map π)
  have hImgq : IsPGroup q (QX.map π) := hQXq.map π
  have hbot : QX.map π = ⊥ :=
    disjoint_self.mp (IsPGroup.disjoint_of_ne 2 q (by omega : 2 ≠ q)
      (QX.map π) (QX.map π) hImg2 hImgq)
  have hQXK : QX ≤ KX := by
    rw [Subgroup.map_eq_bot_iff] at hbot
    have hker : π.ker = KX := by
      simp [π]
    rwa [hker] at hbot
  intro q hq
  have hqX : (⟨q, hQX hq⟩ : ↥X) ∈ QX := hq
  exact hQXK hqX

private theorem caseB_Q_normalizes_zOne (D : Data G) {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hThomp : KThomp)
    {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) {Q : Subgroup G}
    (hQleP : Q ≤ barPreimage D.M (CFSG.pCore q (Bar2 D.M))) (hQq : IsPGroup q ↥Q)
    (hTQ : Permutes D.T Q) (hQN : Q ⊓ c.N = ⊥)
    (hJN : Subgroup.normalizer (F12.jOf D.T : Set G) ≤ c.N) :
    Q ≤ Subgroup.normalizer (zOneOf D.T : Set G) := by
  classical
  have hTNJ : D.T ≤ Subgroup.normalizer (F12.jOf D.T : Set G) := T_le_normalizer_jOf D
  have hQNJ : Q ⊓ Subgroup.normalizer (F12.jOf D.T : Set G) = ⊥ := by
    have hle : Q ⊓ Subgroup.normalizer (F12.jOf D.T : Set G) ≤ Q ⊓ c.N :=
      inf_le_inf_left Q hJN
    rw [hQN] at hle
    exact le_bot_iff.mp hle
  have hDed := caseB_dedekind D hTNJ hQNJ hTQ
  have hThomp' : ((Q ⊔ D.T : Subgroup G) : Set G) =
      (D.T : Set G) * (((Q ⊔ D.T) ⊓ normalizer (zOneOf D.T : Set G) : Subgroup G) : Set G) := by
    rw [thompson_QT D hThomp hq hq5 hQleP hQq hTQ, hDed]
  have hXle : ((Q ⊔ D.T : Subgroup G) : Set G) ⊆
      (((Q ⊔ D.T) ⊓ normalizer (zOneOf D.T : Set G) : Subgroup G) : Set G) := by
    intro x hx
    rw [hThomp'] at hx
    obtain ⟨t, ht, b, hb, rfl⟩ := Set.mem_mul.1 hx
    have htB : t ∈ (Q ⊔ D.T) ⊓ normalizer (zOneOf D.T : Set G) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right ht, T_le_normalizer_zOneOf D ht⟩
    exact Subgroup.mul_mem _ htB hb
  intro x hx
  exact (Subgroup.mem_inf.mp (hXle (Subgroup.mem_sup_left hx))).2

private theorem caseB_normalizer_P₀_le_T (D : Data G) {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {Q X K : Subgroup G}
    (hX : X = Q ⊔ D.T) (hJleK : F12.jOf D.T ≤ K)
    (hQNZ : Q ≤ Subgroup.normalizer (zOneOf D.T : Set G)) (hTQ : Permutes D.T Q)
    (hQN : Q ⊓ c.N = ⊥) (hJN : Subgroup.normalizer (F12.jOf D.T : Set G) ≤ c.N) :
    X ⊓ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G) ≤ D.T := by
  classical
  have hTNJ : D.T ≤ Subgroup.normalizer (F12.jOf D.T : Set G) := T_le_normalizer_jOf D
  have hQNJ : Q ⊓ Subgroup.normalizer (F12.jOf D.T : Set G) = ⊥ := by
    have hle : Q ⊓ Subgroup.normalizer (F12.jOf D.T : Set G) ≤ Q ⊓ c.N :=
      inf_le_inf_left Q hJN
    rw [hQN] at hle
    exact le_bot_iff.mp hle
  have hDed : X ⊓ Subgroup.normalizer (F12.jOf D.T : Set G) = D.T := by
    rw [hX]
    exact caseB_dedekind D hTNJ hQNJ hTQ
  have hJeqP₀ : F12.jOf (D.T ⊓ K) = F12.jOf D.T :=
    jOf_eq_of_le (le_inf (jOf_le_self D.T) hJleK) inf_le_left
  have h1 := CFSG.QuasithinUnique.GammaExtra.normalizer_le_normalizer_thompsonJ (D.T ⊓ K)
  have h2 : CFSG.Quasithin.thompsonJ (D.T ⊓ K) = F12.jOf D.T := by
    rw [← jOf_eq_thompsonJ (D.T ⊓ K), hJeqP₀]
  rw [h2] at h1
  intro y hy
  have hy' : y ∈ X ⊓ Subgroup.normalizer (F12.jOf D.T : Set G) :=
    Subgroup.mem_inf.mpr ⟨hy.1, h1 hy.2⟩
  rwa [hDed] at hy'

private theorem caseB_jOf_le_centralizer_zOne (D : Data G)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z) :
    F12.jOf D.T ≤ Subgroup.centralizer (zOneOf D.T : Set G) := by
  have hZleT : D.Z ≤ D.T := CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le D.T
  have h2 : 2 ≤ CFSG.Open.pRank 2 D.T :=
    hn2.trans (CFSG.SectionRank.pRank_mono (by norm_num) hZleT)
  have hm : 1 < CFSG.pRank 2 ↥D.T := by
    rwa [CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank]
  exact (jOf_le_jOneOf D.T hm).trans (jOneOf_le_centralizer_zOneOf D.T)

private theorem caseB_Q_centralizes_zOne (D : Data G) {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hThomp : KThomp)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    {Q Q₀ : Subgroup G} (hQle : Q ≤ Q₀) (hQq : IsPGroup q ↥Q)
    (hQ₀ : CFSG.ABGLocalTools.IsSylowOf q Q₀
      (barPreimage D.M (CFSG.pCore q (Bar2 D.M)))) (hTQ : Permutes D.T Q)
    (hQN : Q ⊓ c.N = ⊥) (hJN : Subgroup.normalizer (F12.jOf D.T : Set G) ≤ c.N) :
    Q ≤ Subgroup.centralizer (zOneOf D.T : Set G) := by
  have hQleP : Q ≤ barPreimage D.M (CFSG.pCore q (Bar2 D.M)) := hQle.trans hQ₀.le
  have hQNZ : Q ≤ Subgroup.normalizer (zOneOf D.T : Set G) :=
    caseB_Q_normalizes_zOne D c hThomp hq hq5 hQleP hQq hTQ hQN hJN
  have hTZ : D.T ≤ Subgroup.normalizer (zOneOf D.T : Set G) := T_le_normalizer_zOneOf D
  have hZN : Q ⊔ D.T ≤ Subgroup.normalizer (zOneOf D.T : Set G) := sup_le hQNZ hTZ
  have hJleZ1 : F12.jOf D.T ≤ Subgroup.centralizer (zOneOf D.T : Set G) :=
    caseB_jOf_le_centralizer_zOne D hn2
  let X : Subgroup G := Q ⊔ D.T
  let K : Subgroup G := X ⊓ Subgroup.centralizer (zOneOf D.T : Set G)
  have hZX : zOneOf D.T ≤ X := (zOneOf_le D.T).trans le_sup_right
  have hZnorm : ((zOneOf D.T).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZX).mpr hZN
  have hKnormal : (K.subgroupOf X).Normal := by
    simpa [K] using
      CFSG.GroupTheory.CoprimeActionSupport.CentralizerKernel.centralizer_subgroupOf_normal
        hZX hZnorm
  have hKX : K ≤ X := inf_le_left
  have hXK : X ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mp hKnormal
  have hJleX : F12.jOf D.T ≤ X := (jOf_le_self D.T).trans le_sup_right
  have hJleK : F12.jOf D.T ≤ K := le_inf hJleX hJleZ1
  have hQM : Q ≤ D.M := hQleP.trans (uc22p21c_barPreimage_le D.M _)
  have hXM : X ≤ D.M := sup_le hQM D.sylowM.le
  have hTX : CFSG.ABGLocalTools.IsSylowOf 2 D.T X := D.sylowM.of_le le_sup_right hXM
  have hP₀ : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ K) K :=
    hTX.inf_of_le_normalizer hKX hXK
  have hNP₀ : X ⊓ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G) ≤ D.T :=
    caseB_normalizer_P₀_le_T D c rfl hJleK hQNZ hTQ hQN hJN
  have hXsup : X ≤ K ⊔ D.T := caseB_frattini_sup hKX hXK hP₀ hNP₀
  have hQK : Q ≤ K :=
    caseB_qGroup_le_of_sup_two hq (by omega : q ≠ 2) hKX le_sup_right hKnormal hXsup
      D.sylowM.isPGroup hQq le_sup_left
  intro q hqQ
  exact (hQK hqQ).2

private theorem exists_elemAbelian_sq_of_goodQ {q : ℕ} (hq : q.Prime) {Q : Subgroup G}
    (hQq : IsPGroup q ↥Q) (hexp : ∀ x ∈ Q, x ^ q = 1) (hQne : Q ≠ ⊥)
    (hnc : ¬ IsCyclic ↥Q) :
    ∃ E : Subgroup G, E ≤ Q ∧ IsElemAbelian q E ∧ Nat.card E = q ^ 2 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI hQnt : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
  obtain ⟨n, hnpos, hn⟩ :=
    (IsPGroup.nontrivial_iff_card (p := q) (G := ↥Q) (hG := hQq)).mp inferInstance
  have hcard_gt : q < Nat.card ↥Q := by
    have hn1 : n ≠ 1 := by
      intro h1
      apply hnc
      rw [h1, pow_one] at hn
      exact isCyclic_of_prime_card hn
    have hn2 : 1 < n := by omega
    calc q = q ^ 1 := (pow_one q).symm
      _ < q ^ n := Nat.pow_lt_pow_right hq.one_lt hn2
      _ = Nat.card ↥Q := hn.symm
  have hprank_top : 1 < CFSG.Open.pRank q (⊤ : Subgroup ↥Q) :=
    CFSG.one_lt_pRank_of_isPGroup hq hQq hcard_gt fun x =>
      Subtype.ext (by simpa using hexp x x.2)
  have hprankQ : 2 ≤ CFSG.Open.pRank q Q := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup Q]
    exact hprank_top
  have hq_dvd : q ∣ Nat.card ↥Q := by
    rw [hn]
    exact dvd_pow_self q (by omega)
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) q hq_dvd
  let X : Subgroup G := Subgroup.zpowers (x : G)
  have hXQ : X ≤ Q := Subgroup.zpowers_le.mpr x.2
  have hXcard : Nat.card X = q := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hxord]
  obtain ⟨E, -, hEQ, hEel, hEcard⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime hQq hprankQ hXQ hXcard
  exact ⟨E, hEQ, hEel, hEcard⟩

private theorem normalizer_le_of_inf_conj_eq_bot {M Q F : Subgroup G}
    (hFQ : F ≤ Q) (hFM : F ≤ M)
    (hconj : ∀ g : G, g ∉ M → Q ⊓ M.map (MulAut.conj g).toMonoidHom = ⊥)
    (hFne : F ≠ ⊥) : Subgroup.normalizer (F : Set G) ≤ M := by
  intro g hg
  by_contra hgM
  have hFmap : F.map (MulAut.conj g).toMonoidHom = F := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg y).1 hy
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, ?_⟩
      · simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).1 hx
      · change g * (g⁻¹ * x * g) * g⁻¹ = x
        group
  have hle : F ≤ Q ⊓ M.map (MulAut.conj g).toMonoidHom := by
    refine le_inf hFQ ?_
    calc F = F.map (MulAut.conj g).toMonoidHom := hFmap.symm
      _ ≤ M.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hFM
  rw [hconj g hgM] at hle
  exact hFne (le_bot_iff.mp hle)

private theorem caseB_rankThreeGamma_le_of_not_sig (D : Data G) {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h1930 : H1930 D) (h71 : S23_7_1 D Ch) (hsig : D.sig.Nonempty)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Q Q₀ : Subgroup G}
    (hQle : Q ≤ Q₀) (hQq : IsPGroup q ↥Q)
    (hQ₀ : CFSG.ABGLocalTools.IsSylowOf q Q₀
      (barPreimage D.M (CFSG.pCore q (Bar2 D.M))))
    (hexp : ∀ x ∈ Q, x ^ q = 1) (hcl : ⁅⁅Q, Q⁆, Q⁆ = ⊥)
    (hQn : (Q.subgroupOf (D.M ⊓ normalizer (Q₀ : Set G))).Normal)
    (hTQ : Permutes D.T Q) (hQnc : ¬ IsCyclic ↥Q) (hqsig : q ∉ D.sig)
    {E : Subgroup G} (hEQ : E ≤ Q) :
    rankThreeGamma 1 q E ≤ D.M := by
  classical
  have hQ0M : Q₀ ≤ D.M := hQ₀.le.trans (uc22p21c_barPreimage_le D.M _)
  have hQM : Q ≤ D.M := hQle.trans hQ0M
  obtain ⟨p, hp⟩ := hsig
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hpq : p ≠ q := fun h => hqsig (h ▸ hp)
  set P : Subgroup G := barPreimage D.M (CFSG.pCore q (Bar2 D.M)) with hP
  have hPM : P ≤ D.M := uc22p21c_barPreimage_le D.M _
  have hPn : (P.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).mpr uc22p22u_barPreimage_normalizes
  have hPle : P ≤ CFSG.Open.relPPrimeCore p D.M :=
    barPreimage_le_relPPrimeCore (CFSG.pCore_normal (p := q))
      (CFSG.pCore_isPGroup (p := q)) hpp hq hpq hp2
  have hQleM : Q ≤ D.M ⊓ Subgroup.normalizer (Q₀ : Set G) :=
    le_inf hQM (hQle.trans Subgroup.le_normalizer)
  have hconj := h71 h1930 c q hq hq2 Q hQM hQq hQnc hexp hcl p hp P hPM hPn hPle
    Q₀ hQ₀ hQleM hQn
  change CFSG.Open.GLBCore q 1 E ≤ D.M
  refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall ?_
  intro F hFE hF
  have hFQ : F ≤ Q := hFE.trans hEQ
  have hFM : F ≤ D.M := hFQ.trans hQM
  have hFne : F ≠ ⊥ := by
    intro hbot
    have h0 : CFSG.Open.pRank q (⊥ : Subgroup G) = 0 := by
      refine le_antisymm ?_ (Nat.zero_le _)
      refine CFSG.SectionRank.pRank_le hq.one_lt (k := 0) ?_
      intro X hX _
      rw [le_bot_iff] at hX
      rw [hX, Subgroup.card_bot]
      simp
    rw [hbot, h0] at hF
    omega
  exact normalizer_le_of_inf_conj_eq_bot hFQ hFM (fun g hg => hconj g hg) hFne

private theorem caseB_rankThreeGamma_le (D : Data G) {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h1930 : H1930 D) (h6 : S23_6 D Ch) (h71 : S23_7_1 D Ch)
    (hsig : D.sig.Nonempty)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Q Q₀ : Subgroup G}
    (hQle : Q ≤ Q₀) (hQq : IsPGroup q ↥Q)
    (hQ₀ : CFSG.ABGLocalTools.IsSylowOf q Q₀
      (barPreimage D.M (CFSG.pCore q (Bar2 D.M))))
    (hexp : ∀ x ∈ Q, x ^ q = 1) (hcl : ⁅⁅Q, Q⁆, Q⁆ = ⊥)
    (hQn : (Q.subgroupOf (D.M ⊓ normalizer (Q₀ : Set G))).Normal)
    (hTQ : Permutes D.T Q) (hQnc : ¬ IsCyclic ↥Q) {E : Subgroup G} (hEQ : E ≤ Q) :
    rankThreeGamma 1 q E ≤ D.M := by
  classical
  have hQ0M : Q₀ ≤ D.M := hQ₀.le.trans (uc22p21c_barPreimage_le D.M _)
  have hQM : Q ≤ D.M := hQle.trans hQ0M
  by_cases hqsig : q ∈ D.sig
  · have hq_sig1 : q ∈ D.sig1 := by
      have h := h6 h1930 c
      rwa [h] at hqsig
    exact (hsp q hq_sig1).rankThreeGamma_one_le_of_le hq (hQq.to_le hEQ)
      (hEQ.trans hQM)
  · exact caseB_rankThreeGamma_le_of_not_sig D c h1930 h71 hsig hq hq2 hQle hQq
      hQ₀ hexp hcl hQn hTQ hQnc hqsig hEQ

private theorem caseB_A0_core (D : Data G) {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    {A₀ : Subgroup G} (hA0le : A₀ ≤ zJOneOf D.T ⊓ c.V) (hA0card : Nat.card A₀ = 4) :
    A₀ ≤ D.M ∧ A₀ ≠ ⊥ ∧ IsElemAbelian 2 A₀ ∧ A₀ ≤ zOneOf D.T := by
  have hA0V : A₀ ≤ c.V := hA0le.trans inf_le_right
  have hA0zJ : A₀ ≤ zJOneOf D.T := hA0le.trans inf_le_left
  have hA0el : IsElemAbelian 2 A₀ := CFSG.Open.IsElemAbelian.mono hV hA0V
  have hA0M : A₀ ≤ D.M := hA0V.trans ((c.V_le_T h4 h1930).trans D.sylowM.le)
  have hA0ne : A₀ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hA0card
    norm_num at hA0card
  exact ⟨hA0M, hA0ne, hA0el, le_zOneOf_of_le_center hA0zJ fun y hy => hA0el.2 y hy⟩

private theorem caseB_H_core (D : Data G) {A₀ H : Subgroup G}
    (hH : H = Subgroup.normalizer (A₀ : Set G)) (hA0el : IsElemAbelian 2 A₀)
    (hA0M : A₀ ≤ D.M) (hA0ne : A₀ ≠ ⊥) :
    H ≠ ⊤ ∧ CFSG.Open.pCoreOf 2 (H ⊓ D.M) ≠ ⊥ := by
  classical
  haveI : IsSimpleGroup G := D.standing.simple
  have hH2 : IsTwoLocal H := ⟨A₀, hA0ne, hA0el.isPGroup, hH⟩
  have hHne : H ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hH2
  have hA0X : A₀ ≤ H ⊓ D.M := by
    rw [hH]
    exact le_inf Subgroup.le_normalizer hA0M
  haveI hA0Xn : (A₀.subgroupOf (H ⊓ D.M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA0X).mpr (by rw [hH]; exact inf_le_left)
  have hA0sub2 : IsPGroup 2 (A₀.subgroupOf (H ⊓ D.M)) :=
    hA0el.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hA0X).symm
  have hcorele : A₀.subgroupOf (H ⊓ D.M) ≤ CFSG.pCore 2 ↥(H ⊓ D.M) :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup inferInstance hA0sub2
  have hA0core : A₀ ≤ CFSG.Open.pCoreOf 2 (H ⊓ D.M) := by
    rw [CFSG.Open.pCoreOf]
    rw [← Subgroup.map_subgroupOf_eq_of_le hA0X]
    exact Subgroup.map_mono hcorele
  refine ⟨hHne, ?_⟩
  intro hbot
  rw [hbot] at hA0core
  exact hA0ne (le_bot_iff.mp hA0core)

private theorem caseB_false_of_data (D : Data G) {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) (hV : IsElemAbelian 2 c.V)
    (hCaseB : S23_23OmegaCaseB c) (h6 : S23_6 D Ch) (h71 : S23_7_1 D Ch)
    (hsig : D.sig.Nonempty)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h67 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_7 D) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    {Q Q₀ E : Subgroup G} (hQ₀ : CFSG.ABGLocalTools.IsSylowOf q Q₀
      (barPreimage D.M (CFSG.pCore q (Bar2 D.M))))
    (hQle : Q ≤ Q₀) (hQq : IsPGroup q ↥Q) (hexp : ∀ x ∈ Q, x ^ q = 1)
    (hcl : ⁅⁅Q, Q⁆, Q⁆ = ⊥) (hQn : (Q.subgroupOf (D.M ⊓ normalizer (Q₀ : Set G))).Normal)
    (hTQ : Permutes D.T Q) (hQnc : ¬ IsCyclic ↥Q)
    (hQcentZ1 : Q ≤ Subgroup.centralizer (zOneOf D.T : Set G))
    (hEQ : E ≤ Q) (hEel : IsElemAbelian q E) (hEcard : Nat.card E = q ^ 2) : False := by
  obtain ⟨A₀, hA0le, hA0card, x, hxL, hxN, hxM⟩ := hCaseB.2.1
  obtain ⟨hA0M, hA0ne, hA0el, hA0z1⟩ := caseB_A0_core D c hV h4 h1930 hA0le hA0card
  have hQcentA0 : Q ≤ Subgroup.centralizer (A₀ : Set G) :=
    hQcentZ1.trans (Subgroup.centralizer_le hA0z1)
  have hQNA0 : Q ≤ Subgroup.normalizer (A₀ : Set G) :=
    hQcentA0.trans (Subgroup.centralizer_le_normalizer (A₀ : Set G))
  let H : Subgroup G := Subgroup.normalizer (A₀ : Set G)
  have hEH : E ≤ H := hEQ.trans hQNA0
  obtain ⟨hHne, hCoreNe⟩ := caseB_H_core D rfl hA0el hA0M hA0ne
  have hHNleM : ¬ H ≤ D.M := by
    intro hle
    exact hxM (hle hxN)
  have hEM : E ≤ D.M :=
    hEQ.trans (hQle.trans (hQ₀.le.trans (uc22p21c_barPreimage_le D.M _)))
  have hΓ : rankThreeGamma 1 q E ≤ D.M :=
    caseB_rankThreeGamma_le D c h1930 h6 h71 hsig hsp hq (by omega : q ≠ 2) hQle hQq hQ₀
      hexp hcl hQn hTQ hQnc hEQ
  have hres := h67 (by rw [h6 h1930 c]) q hq (by omega : q ≠ 2) E hEM hEel hEcard hΓ H hEH
    hHne hCoreNe hHNleM
  omega

theorem s23_23CaseBFit_of (D : Data G) (Ch : Choice2011 G)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch)
    (hA : KTab23a) (h4 : S23_4 D Ch) (hK : KOrdNatural)
    (h6 : S23_6 D Ch) (h71 : S23_7_1 D Ch) (h72 : S23_7_2 D Ch)
    (h72s : S23_7_2_sig D Ch) (hsig : D.sig.Nonempty)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (hThomp : KThomp) (hKA : KOmA)
    (h67 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_7 D) :
    S23_23CaseBFit D Ch := by
  intro h1930 c hMinus hV hNat hCaseB q hq hq5
  by_contra hYnc
  classical
  have hq2 : q ≠ 2 := by omega
  have hYne : CFSG.pCore q (Bar2 D.M) ≠ ⊥ := by
    intro hbot
    exact hYnc (by rw [hbot]; infer_instance)
  obtain ⟨Q₀, Q, hQ₀, hQle, hQne, hexp, hcl, hQn, hTQ, himp⟩ :=
    exists_good_Q D hq hq2 hYne
  have hQnc : ¬ IsCyclic ↥Q := himp hYnc
  have hQq : IsPGroup q ↥Q := hQ₀.isPGroup.to_le hQle
  have hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z := by
    rw [hCaseB.1]
  have hNatH : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z) := by
    convert hNat using 2
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 2) D.Z]
    exact (CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥D.Z).symm
  have hMinus' : IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z) := by
    convert hMinus using 2
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 2) D.Z]
    exact (CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥D.Z).symm
  have hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L :=
    le_of_eq (Ctx23L.inf_centralizer_V_eq_pCoreOf D Ch h2 h3 h4 hK h1930 c hMinus')
  have hJN : Subgroup.normalizer (F12.jOf D.T : Set G) ≤ c.N :=
    (c.jZero_facts hV hA h4 h1930 hn2 hNatH hKA hCLV).2.2
  have hQN : Q ⊓ c.N = ⊥ :=
    c.inf_N_eq_bot h1930 h72 h72s hsig hq hq2 hQ₀ hQle hexp hcl hQn hTQ
      (Or.inr hQnc)
  have hQcentZ1 : Q ≤ Subgroup.centralizer (zOneOf D.T : Set G) :=
    caseB_Q_centralizes_zOne D c hThomp hn2 hq hq5 hQle hQq hQ₀ hTQ hQN hJN
  obtain ⟨E, hEQ, hEel, hEcard⟩ :=
    exists_elemAbelian_sq_of_goodQ hq hQq hexp hQne hQnc
  exact caseB_false_of_data D c h4 h1930 hV hCaseB h6 h71 hsig hsp h67 hq hq5 hQ₀ hQle
    hQq hexp hcl hQn hTQ hQnc hQcentZ1 hEQ hEel hEcard

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
