module

public import CFSG.Quasithin.Recognition.Stroth.BenderSylow
public import CFSG.Quasithin.Recognition.Stroth.Str83KernelParts
public import CFSG.Quasithin.Background.OddCentralKerSylowTI
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Q
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5L2T

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem psl2_normalizer_transitive {n : ℕ} (hn : 1 ≤ n) {X : Type} [Group X] [Finite X]
    (e : IsL2Quot n X) (T : Sylow 2 X) {x y : X} (hx : x ∈ (T : Subgroup X))
    (hy : y ∈ (T : Subgroup X)) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ d ∈ Subgroup.normalizer ((T : Subgroup X) : Set X), d * x * d⁻¹ = y := by
  obtain ⟨φ⟩ := e
  let L := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)
  let U : Sylow 2 L := T.mapSurjective (f := φ.toMonoidHom) φ.surjective
  have hUcoe : (U : Subgroup L) = (T : Subgroup X).map φ.toMonoidHom :=
    Sylow.coe_mapSurjective (f := φ.toMonoidHom) (hf := φ.surjective) T
  have hxU : φ x ∈ (U : Subgroup L) := by
    rw [hUcoe]
    exact Subgroup.mem_map_of_mem φ.toMonoidHom hx
  have hyU : φ y ∈ (U : Subgroup L) := by
    rw [hUcoe]
    exact Subgroup.mem_map_of_mem φ.toMonoidHom hy
  have hx1' : φ x ≠ 1 := fun h => hx1 (φ.injective (by simpa using h))
  have hy1' : φ y ≠ 1 := fun h => hy1 (φ.injective (by simpa using h))
  obtain ⟨b, hb, hbxy⟩ := CFSG.Quasithin.H13.psl2_sylow_transitive_cs5 hn
    (GaloisField.card 2 n (by omega)) U hxU hx1' hyU hy1'
  have hbN : b ∈ (Subgroup.normalizer ((T : Subgroup X) : Set X)).map φ.toMonoidHom := by
    rw [Subgroup.map_equiv_normalizer_eq (T : Subgroup X) φ]
    rwa [← hUcoe]
  obtain ⟨d, hdN, hdφ⟩ := Subgroup.mem_map.mp hbN
  refine ⟨d, hdN, φ.injective ?_⟩
  have hφd : φ d = b := hdφ
  calc φ (d * x * d⁻¹) = φ d * φ x * (φ d)⁻¹ := by simp
    _ = b * φ x * b⁻¹ := by rw [hφd]
    _ = φ y := hbxy

theorem BenderType.sylowTwoTI {K : Type} [Group K] [Finite K]
    {n i e : ℕ} (h : BenderType K n i e) : SylowTwoTI K := by
  intro P Q hPQ
  obtain ⟨t, hc⟩ := h.exists_benderCore P
  by_contra hne
  exact hPQ (hc.sylow_eq_of_ne_bot hne inf_le_left inf_le_right).symm

theorem statedSU_sylow_inf_eq_bot {n : ℕ} (hn : 2 ≤ n)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2)
    {P Q : Subgroup (StatedSU 3 (2 ^ n) F)}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P ⊤)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q ⊤) (hPQ : P ≠ Q) :
    P ⊓ Q = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : StatedSU 3 (2 ^ n) F →* StatedProj (StatedSU 3 (2 ^ n) F) :=
    QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F))
  have hρ : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hker : ρ.ker = (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F) :=
    QuotientGroup.ker_mk' _
  have hcenter : ρ.ker ≤ Subgroup.center (StatedSU 3 (2 ^ n) F) := by
    rw [hker]
    exact statedSU_scalars_le_center
  have hnot : ¬ Even (Nat.card ((StatedScalars (Fin 3) F).subgroupOf
      (StatedSU 3 (2 ^ n) F))) := by
    rw [even_iff_two_dvd]
    exact CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf
      (M := StatedSU 3 (2 ^ n) F) (d := 3)
      Nat.prime_two (by decide) (by
        intro c hc
        have hdet := det_eq_one_of_mem_statedSU hc
        rw [Matrix.GeneralLinearGroup.det_scalar] at hdet
        simpa using hdet)
  have hodd : Odd (Nat.card ρ.ker) := by
    rw [hker]
    exact Nat.not_even_iff_odd.mp hnot
  obtain ⟨e, hBT⟩ := benderType_statedProj (n := n) (F := F) hn hF
  have hTIproj : SylowTwoTI (StatedProj (StatedSU 3 (2 ^ n) F)) :=
    BenderType.sylowTwoTI hBT
  exact SylowTwoTI.isSylowOf_inf_eq_bot
    (SylowTwoTI.of_central_odd_ker ρ hρ hcenter hodd hTIproj) hP hQ hPQ

theorem str86_oTwoQuot_sylowTwoTI {L : Subgroup G}
    (h : VSzBig L ∨ VU3Big L ∨ ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L)) :
    SylowTwoTI (oTwoQuot ↥L) := by
  rcases h with hSz | hU3L2
  · obtain ⟨a, ha, he⟩ := hSz
    obtain ⟨e⟩ := he
    have hBT : BenderType (CFSG.Theory.Comparator.SzModel a) (2 * a + 1) 2 1 :=
      BenderType.suzuki a ha (MulEquiv.refl (↥(CFSG.Theory.Comparator.SzModel a)))
    exact SylowTwoTI.of_mulEquiv
      (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a)).symm)
      (BenderType.sylowTwoTI hBT)
  · rcases hU3L2 with hU3 | hL2
    · obtain ⟨n, hn, F, hFld, hFin, hFc, hU3⟩ := hU3
      letI : Field F := hFld
      haveI : Finite F := hFin
      rcases hU3 with hSU | hSP
      · obtain ⟨e⟩ := hSU
        have hTI : SylowTwoTI (StatedSU 3 (2 ^ n) F) :=
          SylowTwoTI.of_isSylowOf fun P Q hP hQ hPQ =>
            statedSU_sylow_inf_eq_bot hn hFc hP hQ hPQ
        exact SylowTwoTI.of_mulEquiv e hTI
      · obtain ⟨e⟩ := hSP
        obtain ⟨e', hBT⟩ := benderType_statedProj (n := n) (F := F) hn hFc
        exact SylowTwoTI.of_mulEquiv e (BenderType.sylowTwoTI hBT)
    · obtain ⟨n, hn, he⟩ := hL2
      obtain ⟨e⟩ := he
      exact SylowTwoTI.of_mulEquiv e
        (BenderType.sylowTwoTI
          (BenderType.linear n hn (MulEquiv.refl
            (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)))))

theorem f112_sylow_inf_conj_eq_pCoreOf_left {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (h1 : VSzBig L1 ∨ VU3Big L1 ∨ ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L1))
    {g : G} (hg : g ∈ L1 ⊔ bigB L1 L2 S) (hgB : g ∉ bigB L1 L2 S) :
    S ⊓ (MulAut.conj g • S) = Q1 L1 L2 S := by
  classical
  have hE : S = (S ⊓ L1) ⊔ Q1 L1 L2 S := eq_sup_pCoreOf_of_bender_left hF.1 hSB h1
  have hBL : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    bigB_le_normalizer_of_hyp111 hF.1
  obtain ⟨l, hlL1, b, hbB, hglb⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hBL).mp hg
  have hbN : b ∈ Subgroup.normalizer (S : Set G) := hSB hbB
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hBsyl : bigB L1 L2 S = (L1 ⊔ bigB L1 L2 S) ⊓
      Subgroup.normalizer ((S ⊓ L1 : Subgroup G) : Set G) :=
    F1.bigB_eq_parabolic_inf hR
  have hP1N : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    sup_le Subgroup.le_normalizer hBL
  have hNP1 : Subgroup.normalizer (S : Set G) ⊓ (L1 ⊔ bigB L1 L2 S) ≤
      bigB L1 L2 S := by
    intro x hx
    obtain ⟨hxN, hxP⟩ := Subgroup.mem_inf.mp hx
    rw [hBsyl]
    exact Subgroup.mem_inf.mpr ⟨hxP, Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨hxN, hP1N hxP⟩)⟩
  have hlN : l ∉ Subgroup.normalizer (S : Set G) := by
    intro hl
    apply hgB
    have hlB : l ∈ bigB L1 L2 S :=
      hNP1 (Subgroup.mem_inf.mpr ⟨hl, Subgroup.mem_sup_left hlL1⟩)
    rw [hglb]
    exact (bigB L1 L2 S).mul_mem hlB hbB
  have hSne : S ≠ MulAut.conj l • S := by
    intro hEq
    exact hlN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEq.symm)
  have hH : L1 ⊔ Q1 L1 L2 S = L1 ⊔ S := by
    nth_rw 2 [hE]
    rw [← sup_assoc, sup_eq_left.mpr (inf_le_right : S ⊓ L1 ≤ L1)]
  have hSleH : S ≤ L1 ⊔ Q1 L1 L2 S := by
    rw [hH]
    exact le_sup_right
  have hHnorm : MulAut.conj l • (L1 ⊔ Q1 L1 L2 S) = L1 ⊔ Q1 L1 L2 S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer (Subgroup.mem_sup_left hlL1))
  have hSleH' : MulAut.conj l • S ≤ L1 ⊔ Q1 L1 L2 S := by
    calc MulAut.conj l • S ≤ MulAut.conj l • (L1 ⊔ Q1 L1 L2 S) :=
          Subgroup.map_mono hSleH
      _ = L1 ⊔ Q1 L1 L2 S := hHnorm
  have hQleH : Q1 L1 L2 S ≤ L1 ⊔ Q1 L1 L2 S := le_sup_right
  have hSylH : IsSylowTwoOf S (L1 ⊔ Q1 L1 L2 S) := isSylowTwoOf_sup_pCoreOf hF.1 hE
  have hSylH' : IsSylowTwoOf (MulAut.conj l • S) (L1 ⊔ Q1 L1 L2 S) := by
    have h := CFSG.Quasithin.F7.isSylowTwoOf_conj hSylH l
    have h2 : CFSG.Quasithin.conjSub l (L1 ⊔ Q1 L1 L2 S) =
        L1 ⊔ Q1 L1 L2 S := hHnorm
    rwa [show CFSG.Quasithin.conjSub l S = MulAut.conj l • S from rfl, h2] at h
  have hSsub : CFSG.ABGLocalTools.IsSylowOf 2 (S.subgroupOf (L1 ⊔ Q1 L1 L2 S)) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, hSylH.2.1.comap_subtype, by simpa using hSylH.2.2⟩
  have hSsub' : CFSG.ABGLocalTools.IsSylowOf 2
      ((MulAut.conj l • S).subgroupOf (L1 ⊔ Q1 L1 L2 S)) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr
      ⟨le_top, hSylH'.2.1.comap_subtype, by simpa using hSylH'.2.2⟩
  have hQleS : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF)
  have hNsub : (Q1 L1 L2 S).subgroupOf (L1 ⊔ Q1 L1 L2 S) ≤
      S.subgroupOf (L1 ⊔ Q1 L1 L2 S) := Subgroup.subgroupOf_mono _ hQleS
  have hQnorm : MulAut.conj l • Q1 L1 L2 S = Q1 L1 L2 S := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mp ?_
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P1 L1 L2 S))
      ((le_sup_left : L1 ≤ P1 L1 L2 S) hlL1)
  have hQleS' : Q1 L1 L2 S ≤ MulAut.conj l • S := by
    calc Q1 L1 L2 S = MulAut.conj l • Q1 L1 L2 S := hQnorm.symm
      _ ≤ MulAut.conj l • S := Subgroup.map_mono hQleS
  have hNsub' : (Q1 L1 L2 S).subgroupOf (L1 ⊔ Q1 L1 L2 S) ≤
      (MulAut.conj l • S).subgroupOf (L1 ⊔ Q1 L1 L2 S) :=
    Subgroup.subgroupOf_mono _ hQleS'
  have hPQsub : S.subgroupOf (L1 ⊔ Q1 L1 L2 S) ≠
      (MulAut.conj l • S).subgroupOf (L1 ⊔ Q1 L1 L2 S) := by
    intro h
    apply hSne
    have h2 : S ⊓ (L1 ⊔ Q1 L1 L2 S) =
        (MulAut.conj l • S) ⊓ (L1 ⊔ Q1 L1 L2 S) := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hSleH, inf_eq_left.mpr hSleH'] at h2
  have hpCore : CFSG.pCore 2 ↥(L1 ⊔ Q1 L1 L2 S) =
      (Q1 L1 L2 S).subgroupOf (L1 ⊔ Q1 L1 L2 S) := by
    apply Subgroup.map_injective (L1 ⊔ Q1 L1 L2 S).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le
      (le_sup_right : Q1 L1 L2 S ≤ L1 ⊔ Q1 L1 L2 S)]
    exact pCoreOf_sup_pCoreOf hF.1
  have hTI : SylowTwoTI (↥(L1 ⊔ Q1 L1 L2 S) ⧸
      CFSG.pCore 2 ↥(L1 ⊔ Q1 L1 L2 S)) :=
    SylowTwoTI.of_mulEquiv (oTwoQuotSupEquiv hF.1)
      (str86_oTwoQuot_sylowTwoTI h1)
  have hNP : CFSG.pCore 2 ↥(L1 ⊔ Q1 L1 L2 S) ≤ S.subgroupOf (L1 ⊔ Q1 L1 L2 S) := by
    rw [hpCore]
    exact hNsub
  have hNQ : CFSG.pCore 2 ↥(L1 ⊔ Q1 L1 L2 S) ≤
      (MulAut.conj l • S).subgroupOf (L1 ⊔ Q1 L1 L2 S) := by
    rw [hpCore]
    exact hNsub'
  have hfin : S.subgroupOf (L1 ⊔ Q1 L1 L2 S) ⊓
      (MulAut.conj l • S).subgroupOf (L1 ⊔ Q1 L1 L2 S) =
      (Q1 L1 L2 S).subgroupOf (L1 ⊔ Q1 L1 L2 S) := by
    have hpc := SylowTwoTI.inf_eq_of_sylowTwoTI_quotient
      (CFSG.pCore 2 ↥(L1 ⊔ Q1 L1 L2 S)) hTI hSsub hSsub' hNP hNQ hPQsub
    rwa [hpCore] at hpc
  have hfinG : S ⊓ (MulAut.conj l • S) = Q1 L1 L2 S := by
    have hmap : (S ⊓ (MulAut.conj l • S)).subgroupOf (L1 ⊔ Q1 L1 L2 S) =
        (Q1 L1 L2 S).subgroupOf (L1 ⊔ Q1 L1 L2 S) := by
      rw [← Subgroup.comap_subtype (S ⊓ (MulAut.conj l • S)) (L1 ⊔ Q1 L1 L2 S),
        Subgroup.comap_inf, Subgroup.comap_subtype S (L1 ⊔ Q1 L1 L2 S),
        Subgroup.comap_subtype (MulAut.conj l • S) (L1 ⊔ Q1 L1 L2 S)]
      exact hfin
    have h2 := Subgroup.subgroupOf_inj.mp hmap
    rwa [inf_eq_left.mpr (inf_le_left.trans hSleH), inf_eq_left.mpr hQleH] at h2
  have hconj : MulAut.conj g • S = MulAut.conj l • S := by
    rw [hglb, map_mul, mul_smul,
      show MulAut.conj b • S = S from Subgroup.mem_normalizer_iff_map_conj_eq.mp hbN]
  rw [hconj]
  exact hfinG

theorem f112_sylow_inf_conj_eq_pCoreOf_right {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (h2 : VSzBig L2 ∨ VU3Big L2 ∨ ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L2))
    {g : G} (hg : g ∈ L2 ⊔ bigB L1 L2 S) (hgB : g ∉ bigB L1 L2 S) :
    S ⊓ (MulAut.conj g • S) = Q2 L1 L2 S := by
  have h := f112_sylow_inf_conj_eq_pCoreOf_left (L1 := L2) (L2 := L1) (S := S) hF.symm
    (by simpa [bigB_comm] using hSB) h2 (by simpa [bigB_comm] using hg)
    (by simpa [bigB_comm] using hgB)
  have hQ : Q1 L2 L1 S = Q2 L1 L2 S := by
    simp only [Q1, Q2, P1, P2, bigB_comm]
  rw [hQ] at h
  exact h

theorem str86_bigB_le_normalizer (hO : Str86Orders)
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) (h1 : VU3Big L1) (hB2 : VBig L2)
    (h2 : VL2 L2) :
    (S ⊓ L1) ⊔ (S ⊓ L2) = S ∧
      bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) := by
  obtain ⟨k, hk, F, hField, hFin, hFc, hU3⟩ := h1
  letI : Field F := hField
  haveI : Finite F := hFin
  have hF' : F112Hyp L1 L2 ((S ⊓ L1) ⊔ (S ⊓ L2)) := f112Hyp_sup_inf hF
  have hS := hO G L1 L2 S k F hF hk hFc hU3 hB2 h2
  have hS' := hO G L1 L2 ((S ⊓ L1) ⊔ (S ⊓ L2)) k F hF' hk hFc hU3 hB2 h2
  have hcard : Nat.card S = Nat.card ↥((S ⊓ L1) ⊔ (S ⊓ L2)) := by
    rw [hS.2.2.2, hS'.2.2.2]
  have hle : (S ⊓ L1) ⊔ (S ⊓ L2) ≤ S := sup_le inf_le_left inf_le_left
  have heq : (S ⊓ L1) ⊔ (S ⊓ L2) = S :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)
  exact ⟨heq, bigB_le_normalizer_of_sup_inf_eq hF.1 heq⟩

theorem str86_pCoreOf_sup_pCoreOf
    {L1 L2 S : Subgroup G} {n : ℕ} (hF : F112HypW L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (h1 : VSzBig L1 ∨ VU3Big L1) (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) :
    Q1 L1 L2 S ⊔ Q2 L1 L2 S = S := by
  classical
  let P1 : Subgroup G := L1 ⊔ bigB L1 L2 S
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  let Q1 : Subgroup G := pCoreOf 2 P1
  let Q2 : Subgroup G := pCoreOf 2 P2
  let R : Subgroup G := Q1 ⊔ Q2
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hBnorm : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) := hSB
  have hE1 : S = (S ⊓ L1) ⊔ Q1 :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB (h1.elim Or.inl fun h => Or.inr (Or.inl h))
  have hE2 : S = (S ⊓ L2) ⊔ Q2 :=
    eq_sup_pCoreOf_of_bender_right hF.1 hSB (Or.inr (Or.inr ⟨n, hn, hL2⟩))
  have h7 : ¬ Q1 ≤ Q2 :=
    not_pCoreOf_le_pCoreOf hF hSB hE1 h1
  have hQ1leS : Q1 ≤ S := CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF)
  have hQ2leS : Q2 ≤ S := CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF)
  have hRleS : R ≤ S := sup_le hQ1leS hQ2leS
  have hRne : R ≠ Q2 := by
    intro h
    exact h7 (h ▸ le_sup_left)
  obtain ⟨D2, hD2cart, hD2inf, hD2sup⟩ := F1.exists_cartan hF.1.h2.sylow
  have hD2leB2 : D2 ≤ borelOf L2 S := hD2cart.1
  have hD2odd : Odd (Nat.card ↥D2) := hD2cart.2.1
  have hD2leL2 : D2 ≤ L2 := hD2leB2.trans (F1.borelOf_le L2 S)
  have hD2infO : D2 ⊓ pCoreOf 2 L2 = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxD, hxO⟩ := Subgroup.mem_inf.mp hx
    have hxS : x ∈ S :=
      (Subgroup.mem_inf.mp (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hF.1.h2.sylow hxO)).1
    have hxL2 : x ∈ L2 := hD2leL2 hxD
    have hxS2 : x ∈ S ⊓ L2 := Subgroup.mem_inf.mpr ⟨hxS, hxL2⟩
    have hxbot : x ∈ D2 ⊓ (S ⊓ L2) := Subgroup.mem_inf.mpr ⟨hxD, hxS2⟩
    rw [hD2inf] at hxbot
    exact Subgroup.mem_bot.mp hxbot
  let K : Type := oTwoQuot ↥L2
  let π : ↥L2 →* K := QuotientGroup.mk' (pCore 2 ↥L2)
  let S2 : Subgroup G := S ⊓ L2
  let Qimg : Subgroup K := (S2.subgroupOf L2).map π
  let Dbar : Subgroup K := (D2.subgroupOf L2).map π
  have hmapB := F1.map_borelOf_eq_normalizer hF.1.h2.sylow
  obtain ⟨hQimg2, hQimgodd, hMmap⟩ := hmapB
  let Q : Sylow 2 K := hQimg2.toSylow hQimgodd
  have hQcoe : (Q : Subgroup K) = Qimg := IsPGroup.toSylow_coe hQimg2 hQimgodd
  obtain ⟨e2⟩ := hL2
  have hBT2 : BenderType K n 1 1 := BenderType.linear n hn e2
  have hBoreleq : ((borelOf L2 S).subgroupOf L2).map π = borel (Q : Subgroup K) := by
    rw [CFSG.GH74.Uniqueness.Bender.borel, hQcoe, hMmap]
  have hDbarLe : Dbar ≤ borel (Q : Subgroup K) := by
    rw [← hBoreleq]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono L2 hD2leB2)
  have hSupD : (Q : Subgroup K) ⊔ Dbar = borel (Q : Subgroup K) := by
    have h1 : ((S2 ⊔ D2).subgroupOf L2).map π = borel (Q : Subgroup K) := by
      rw [hD2sup]
      exact hBoreleq
    have hsub : (S2 ⊔ D2).subgroupOf L2 = S2.subgroupOf L2 ⊔ D2.subgroupOf L2 :=
      CFSG.ComponentClassification.GSThmB.subgroupOf_sup_of_le
        (inf_le_right : S2 ≤ L2) hD2leL2
    have h2 : ((S2.subgroupOf L2) ⊔ (D2.subgroupOf L2)).map π =
        ((S2 ⊔ D2).subgroupOf L2).map π := by
      rw [hsub]
    rw [hQcoe]
    change Qimg ⊔ Dbar = borel (Q : Subgroup K)
    rw [show Qimg ⊔ Dbar = ((S2.subgroupOf L2) ⊔ (D2.subgroupOf L2)).map π from
      (Subgroup.map_sup _ _ _).symm]
    rw [h2]
    exact h1
  have hDbarOdd : Odd (Nat.card ↥Dbar) := by
    let fD : ↥(D2.subgroupOf L2) →* K :=
      π.comp (D2.subgroupOf L2).subtype
    have hinj : Function.Injective fD := by
      intro a b hab
      have h1 : π (((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2)) = 1 := by
        have hcoe : ((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2) =
            (a : ↥L2)⁻¹ * (b : ↥L2) := by simp
        rw [hcoe, map_mul, map_inv]
        have hab' : π ((a : ↥L2)) = π ((b : ↥L2)) := hab
        rw [hab']
        simp
      have h2 : ((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2) ∈ pCore 2 ↥L2 := by
        rw [← QuotientGroup.ker_mk' (pCore 2 ↥L2)]
        exact MonoidHom.mem_ker.mpr h1
      have h3 : ((((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2)) : G) ∈ pCoreOf 2 L2 :=
        (F1.mem_pCore_iff_coe _).mp h2
      have h4 : (((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2) : G) ∈ D2 :=
        Subgroup.mem_subgroupOf.mp (a⁻¹ * b).2
      have h5 : (((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2) : G) = 1 := by
        have hx : (((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2) : G) ∈ D2 ⊓ pCoreOf 2 L2 :=
          Subgroup.mem_inf.mpr ⟨h4, h3⟩
        rw [hD2infO] at hx
        exact Subgroup.mem_bot.mp hx
      have h6 : a⁻¹ * b = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        exact h5
      exact inv_mul_eq_one.mp h6
    have hcard : Nat.card ↥Dbar = Nat.card ↥D2 := by
      have hDbar_eq : Dbar = (⊤ : Subgroup ↥(D2.subgroupOf L2)).map fD := by
        change (D2.subgroupOf L2).map π = Subgroup.map fD ⊤
        rw [← MonoidHom.range_eq_map]
        ext z
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨⟨y, hy⟩, rfl⟩
        · rintro ⟨x, rfl⟩
          exact ⟨(x : ↥L2), x.2, rfl⟩
      rw [hDbar_eq, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD2leL2).toEquiv]
    rw [hcard]
    exact hD2odd
  obtain ⟨t, ht2, htnot, hcartan⟩ :=
    exists_involution_cartan_eq hBT2 Q hDbarLe hDbarOdd hSupD
  obtain ⟨t0, hc0⟩ := hBT2.exists_benderCore Q
  have hc : BenderCore (2 ^ n) 1 1 (Q : Subgroup K) t :=
    hc0.of_involution ht2 htnot
  have hroot : rootCenter (Q : Subgroup K) = (Q : Subgroup K) := by
    apply Subgroup.eq_of_le_of_card_ge (rootCenter_le _)
    rw [hc0.card_center, hc0.card_eq, pow_one]
  have hTrans : ∀ x ∈ (Q : Subgroup K), x ≠ 1 → ∀ y ∈ (Q : Subgroup K), y ≠ 1 →
      ∃ d ∈ Dbar, d⁻¹ * x * d = y := by
    intro x hx hx1 y hy hy1
    have hxZ : x ∈ rootCenter (Q : Subgroup K) := by rw [hroot]; exact hx
    have hyZ : y ∈ rootCenter (Q : Subgroup K) := by rw [hroot]; exact hy
    obtain ⟨d, hd, hdy⟩ := hc.exists_cartan_conj hxZ hx1 hyZ hy1
    exact ⟨d, by rwa [hcartan] at hd, hdy.symm⟩
  have hBleP1 : bigB L1 L2 S ≤ P1 := le_sup_right
  have hBleP2 : bigB L1 L2 S ≤ P2 := le_sup_right
  have hBR : bigB L1 L2 S ≤ Subgroup.normalizer (R : Set G) :=
    F1.le_normalizer_sup
      (hBleP1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P1))
      (hBleP2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P2))
  have hSleP2 : S ≤ P2 := (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hQ2N : S ≤ Subgroup.normalizer (Q2 : Set G) :=
    hSleP2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P2)
  have hD2leP2 : D2 ≤ P2 := hD2leL2.trans le_sup_left
  have hD2N : D2 ≤ Subgroup.normalizer (Q2 : Set G) :=
    hD2leP2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P2)
  have hcoset : ∀ r s : G, r ∈ R → r ∉ Q2 → s ∈ S → s ∉ Q2 →
      ∃ d ∈ D2, ∃ q ∈ Q2, d⁻¹ * r * d = q * s := by
    intro r s hrR hrQ2 hsS hsQ2
    have hrE : r ∈ (S ⊓ L2) ⊔ Q2 := by rw [← hE2]; exact hRleS hrR
    have hsE : s ∈ (S ⊓ L2) ⊔ Q2 := by rw [← hE2]; exact hsS
    have hQ2leP2 : Q2 ≤ P2 := CFSG.LieType.BorelTits.pCoreOf_le 2 P2
    have hQ2leB : Q2 ≤ bigB L1 L2 S := hQ2leS.trans le_sup_right
    have hQ2N_S : Q2 ≤ Subgroup.normalizer (S : Set G) := hQ2leB.trans hBnorm
    have hP2N : P2 ≤ Subgroup.normalizer (L2 : Set G) :=
      sup_le Subgroup.le_normalizer (by
        simpa [bigB_comm] using bigB_le_normalizer_of_hyp111 hF.1.symm)
    have hQ2N_L2 : Q2 ≤ Subgroup.normalizer (L2 : Set G) := hQ2leP2.trans hP2N
    have hQ2N_S2 : Q2 ≤ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) := by
      intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf
        (Subgroup.mem_inf.mpr ⟨hQ2N_S hx, hQ2N_L2 hx⟩)
    obtain ⟨r2, hr2S2, qr, hqrQ2, hr_eq⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hQ2N_S2).mp hrE
    obtain ⟨s2, hs2S2, qs, hqsQ2, hs_eq⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hQ2N_S2).mp hsE
    have hr2L : r2 ∈ L2 := (Subgroup.mem_inf.mp hr2S2).2
    have hs2L : s2 ∈ L2 := (Subgroup.mem_inf.mp hs2S2).2
    let xbar : K := π ⟨r2, hr2L⟩
    let ybar : K := π ⟨s2, hs2L⟩
    have hxbarQ : xbar ∈ (Q : Subgroup K) := by
      rw [hQcoe]
      exact Subgroup.mem_map.mpr ⟨⟨r2, hr2L⟩, Subgroup.mem_subgroupOf.mpr hr2S2, rfl⟩
    have hybarQ : ybar ∈ (Q : Subgroup K) := by
      rw [hQcoe]
      exact Subgroup.mem_map.mpr ⟨⟨s2, hs2L⟩, Subgroup.mem_subgroupOf.mpr hs2S2, rfl⟩
    have hxbar1 : xbar ≠ 1 := by
      intro h
      apply hrQ2
      have hmem : (⟨r2, hr2L⟩ : ↥L2) ∈ pCore 2 ↥L2 := by
        rw [← QuotientGroup.ker_mk' (pCore 2 ↥L2)]
        exact MonoidHom.mem_ker.mpr h
      have hr2O : r2 ∈ pCoreOf 2 L2 := (F1.mem_pCore_iff_coe _).mp hmem
      have hr2Q2 : r2 ∈ Q2 := by
        simpa [Q2, P2, bigB_comm] using
          (CFSG.Quasithin.Hyp111.pCoreOf_le_pCoreOf_vertex hF.1.symm) hr2O
      rw [hr_eq]
      exact Q2.mul_mem hr2Q2 hqrQ2
    have hybar1 : ybar ≠ 1 := by
      intro h
      apply hsQ2
      have hmem : (⟨s2, hs2L⟩ : ↥L2) ∈ pCore 2 ↥L2 := by
        rw [← QuotientGroup.ker_mk' (pCore 2 ↥L2)]
        exact MonoidHom.mem_ker.mpr h
      have hs2O : s2 ∈ pCoreOf 2 L2 := (F1.mem_pCore_iff_coe _).mp hmem
      have hs2Q2 : s2 ∈ Q2 := by
        simpa [Q2, P2, bigB_comm] using
          (CFSG.Quasithin.Hyp111.pCoreOf_le_pCoreOf_vertex hF.1.symm) hs2O
      rw [hs_eq]
      exact Q2.mul_mem hs2Q2 hqsQ2
    obtain ⟨dbar, hdDbar, hdbarconj⟩ := hTrans xbar hxbarQ hxbar1 ybar hybarQ hybar1
    obtain ⟨d2, hd2mem, hd2eq⟩ := Subgroup.mem_map.mp hdDbar
    let d : G := ((d2 : ↥L2) : G)
    have hdD2 : d ∈ D2 := Subgroup.mem_subgroupOf.mp hd2mem
    have hdL2 : d ∈ L2 := (d2 : ↥L2).2
    have hdπ : π (d2 : ↥L2) = dbar := hd2eq
    have hdP2 : d ∈ P2 := hD2leP2 hdD2
    have hqQ2 : d⁻¹ * qr * d ∈ Q2 := by
      have hdN : d⁻¹ ∈ Subgroup.normalizer (Q2 : Set G) :=
        (Subgroup.normalizer (Q2 : Set G)).inv_mem (hD2N hdD2)
      have h := (Subgroup.mem_normalizer_iff.mp hdN qr).mp hqrQ2
      simpa using h
    have hA : d⁻¹ * r2 * d * s2⁻¹ ∈ Q2 := by
      have hdL : d⁻¹ * r2 * d ∈ L2 :=
        L2.mul_mem (L2.mul_mem (L2.inv_mem hdL2) hr2L) hdL2
      have hAL : d⁻¹ * r2 * d * s2⁻¹ ∈ L2 :=
        L2.mul_mem hdL (L2.inv_mem hs2L)
      have himg : π ⟨d⁻¹ * r2 * d * s2⁻¹, hAL⟩ = 1 := by
        have h1 : π ⟨d⁻¹ * r2 * d, hdL⟩ = ybar := by
          have hdπ' : π (d2 : ↥L2) = dbar := hdπ
          have hx : π ⟨r2, hr2L⟩ = xbar := rfl
          have hy : π ⟨s2, hs2L⟩ = ybar := rfl
          have hcoe : (⟨d⁻¹ * r2 * d, hdL⟩ : ↥L2) =
              (d2 : ↥L2)⁻¹ * ⟨r2, hr2L⟩ * (d2 : ↥L2) := by
            apply Subtype.ext
            simp [d]
          rw [hcoe, map_mul, map_mul, map_inv, hdπ', hx]
          exact hdbarconj
        have hcoe2 : (⟨d⁻¹ * r2 * d * s2⁻¹, hAL⟩ : ↥L2) =
            ⟨d⁻¹ * r2 * d, hdL⟩ * ⟨s2, hs2L⟩⁻¹ := by
          apply Subtype.ext
          simp
        rw [hcoe2, map_mul, map_inv, h1]
        rw [show π ⟨s2, hs2L⟩ = ybar from rfl]
        simp
      have hmem : (⟨d⁻¹ * r2 * d * s2⁻¹, hAL⟩ : ↥L2) ∈ pCore 2 ↥L2 := by
        rw [← QuotientGroup.ker_mk' (pCore 2 ↥L2)]
        exact MonoidHom.mem_ker.mpr himg
      have hO : d⁻¹ * r2 * d * s2⁻¹ ∈ pCoreOf 2 L2 :=
        (F1.mem_pCore_iff_coe _).mp hmem
      simpa [Q2, P2, bigB_comm] using
        (CFSG.Quasithin.Hyp111.pCoreOf_le_pCoreOf_vertex hF.1.symm) hO
    have hq' : s2 * ((d⁻¹ * qr * d) * qs⁻¹) * s2⁻¹ ∈ Q2 := by
      have hX : (d⁻¹ * qr * d) * qs⁻¹ ∈ Q2 := Q2.mul_mem hqQ2 (Q2.inv_mem hqsQ2)
      have hs2S : s2 ∈ S := hs2S2.1
      have hs2N : s2 ∈ Subgroup.normalizer (Q2 : Set G) := hQ2N hs2S
      exact (Subgroup.mem_normalizer_iff.mp hs2N _).mp hX
    have hprod : d⁻¹ * r * d * s⁻¹ ∈ Q2 := by
      have hq'' : s2 * ((d⁻¹ * qr * d) * qs⁻¹) * s2⁻¹ ∈ Q2 := hq'
      have hgroup : d⁻¹ * r * d * s⁻¹ =
          (d⁻¹ * r2 * d * s2⁻¹) * (s2 * ((d⁻¹ * qr * d) * qs⁻¹) * s2⁻¹) := by
        rw [hr_eq, hs_eq]
        group
      rw [hgroup]
      exact Q2.mul_mem hA hq''
    refine ⟨d, hdD2, d⁻¹ * r * d * s⁻¹, hprod, ?_⟩
    group
  obtain ⟨r, hrR, hrQ2⟩ : ∃ r : G, r ∈ R ∧ r ∉ Q2 := by
    by_contra h
    push Not at h
    exact hRne (le_antisymm (fun x hx => h x hx) le_sup_right)
  have hD2leB : D2 ≤ bigB L1 L2 S := hD2leB2.trans (le_sup_right.trans le_sup_left)
  have hS_le_R : S ≤ R := by
    intro s hsS
    by_cases hsQ2 : s ∈ Q2
    · exact (le_sup_right : Q2 ≤ R) hsQ2
    · obtain ⟨d, hdD2, q, hqQ2, hdq⟩ := hcoset r s hrR hrQ2 hsS hsQ2
      have hdR : d⁻¹ * r * d ∈ R := by
        have hdN : d⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
          (Subgroup.normalizer (R : Set G)).inv_mem (hBR (hD2leB hdD2))
        have h := (Subgroup.mem_normalizer_iff.mp hdN r).mp hrR
        simpa using h
      have hs_eq : s = q⁻¹ * (d⁻¹ * r * d) := by
        rw [hdq]
        group
      rw [hs_eq]
      exact R.mul_mem ((le_sup_right : Q2 ≤ R) (Q2.inv_mem hqQ2)) hdR
  have hRS : R = S := le_antisymm hRleS hS_le_R
  simpa [R] using hRS

end CFSG.Quasithin.Stroth
