module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndAction
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CComponents
import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath
import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenSylow
import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace A10Five

open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open scoped commutatorElement

private lemma fixedPoints_zpowers_eq_inf_centralizer {X : Type*} [Group X] [Finite X]
    {Q : Subgroup X} {f : X}
    [Fact (Subgroup.zpowers f ≤ Subgroup.normalizer (Q : Set X))] :
    MulAction.fixedPoints (Subgroup.zpowers f) ↥Q =
      ((Q ⊓ Subgroup.centralizer (Subgroup.zpowers f : Set X)).subgroupOf Q : Set ↥Q) := by
  classical
  letI : Subgroup.Normalizes (Subgroup.zpowers f) Q := ⟨Fact.out⟩
  ext x
  rw [MulAction.mem_fixedPoints]
  constructor
  · intro hx
    change x ∈ (Q ⊓ Subgroup.centralizer (Subgroup.zpowers f : Set X)).subgroupOf Q
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h' : (a : X) * (x : X) * (a : X)⁻¹ = (x : X) :=
      congrArg Subtype.val (hx ⟨a, ha⟩)
    calc a * (x : X) = ((a : X) * (x : X) * (a : X)⁻¹) * a := by group
      _ = (x : X) * a := by rw [h']
  · intro hx
    change x ∈ (Q ⊓ Subgroup.centralizer (Subgroup.zpowers f : Set X)).subgroupOf Q at hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_inf] at hx
    intro a
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.2
    apply Subtype.ext
    change (a : X) * (x : X) * (a : X)⁻¹ = (x : X)
    have hxf : f * (x : X) = (x : X) * f :=
      (Subgroup.mem_centralizer_iff.mp hx.2) f (Subgroup.mem_zpowers f)
    rw [← hn]
    have hcomm : Commute (f ^ n) (x : X) := (show Commute f (x : X) from hxf).zpow_left n
    calc f ^ n * (x : X) * (f ^ n)⁻¹ = ((x : X) * f ^ n) * (f ^ n)⁻¹ := by rw [hcomm]
      _ = (x : X) := by group

private lemma card_inf_centralizer_zpowers {X : Type*} [Group X] [Finite X]
    {Q : Subgroup X} {f : X} (hf : Nat.card (Subgroup.zpowers f) = 5)
    (hfQ : Subgroup.zpowers f ≤ Subgroup.normalizer (Q : Set X)) (hQ : Nat.card Q = 27) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer (Subgroup.zpowers f : Set X)) = 27 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hA5 : IsPGroup 5 (Subgroup.zpowers f) :=
    IsPGroup.of_card (n := 1) (by rw [hf]; norm_num)
  haveI : Fact (Subgroup.zpowers f ≤ Subgroup.normalizer (Q : Set X)) := ⟨hfQ⟩
  letI : Subgroup.Normalizes (Subgroup.zpowers f) Q := ⟨hfQ⟩
  have hCsub := fixedPoints_zpowers_eq_inf_centralizer (Q := Q) (f := f)
  have hcard : Nat.card ↥(MulAction.fixedPoints (Subgroup.zpowers f) ↥Q) =
      Nat.card ↥(Q ⊓ Subgroup.centralizer (Subgroup.zpowers f : Set X)) := by
    rw [hCsub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmod := hA5.card_modEq_card_fixedPoints ↥Q
  have hmodC : Nat.card ↥(Q ⊓ Subgroup.centralizer (Subgroup.zpowers f : Set X)) ≡ 27 [MOD 5] := by
    rw [hcard, hQ] at hmod
    exact hmod.symm
  have hdvd : Nat.card ↥(Q ⊓ Subgroup.centralizer (Subgroup.zpowers f : Set X)) ∣ 27 := by
    rw [← hQ]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hdvd' : Nat.card ↥(Q ⊓ Subgroup.centralizer (Subgroup.zpowers f : Set X)) ∣ 3 ^ 3 := by
    simpa using hdvd
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdvd'
  have hk3 : k ≤ 3 := by simpa using hk_le
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · rw [hk] at hmodC; norm_num at hmodC
  · rw [hk] at hmodC; norm_num at hmodC
  · rw [hk] at hmodC; norm_num at hmodC
  · rw [hk]; norm_num

private lemma inf_centralizer_zpowers_eq_of_card_eq_27 {X : Type*} [Group X] [Finite X]
    {Q : Subgroup X} {f : X} (hf : Nat.card (Subgroup.zpowers f) = 5)
    (hfQ : Subgroup.zpowers f ≤ Subgroup.normalizer (Q : Set X)) (hQ : Nat.card Q = 27) :
    Q ⊓ Subgroup.centralizer (Subgroup.zpowers f : Set X) = Q := by
  have hcard := card_inf_centralizer_zpowers hf hfQ hQ
  exact Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hQ, hcard])

theorem mem_centralizer_of_orderOf_eq_five {X : Type*} [Group X] [Finite X] {Q : Subgroup X}
    (hQ : Nat.card Q = 27) {f : X} (hf : orderOf f = 5)
    (hfQ : f ∈ Subgroup.normalizer (Q : Set X)) : f ∈ Subgroup.centralizer (Q : Set X) := by
  classical
  have hA : Nat.card (Subgroup.zpowers f) = 5 := by rw [Nat.card_zpowers, hf]
  haveI : Fact (Subgroup.zpowers f ≤ Subgroup.normalizer (Q : Set X)) :=
    ⟨Subgroup.zpowers_le.mpr hfQ⟩
  have htop := inf_centralizer_zpowers_eq_of_card_eq_27 hA (Subgroup.zpowers_le.mpr hfQ) hQ
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hqC : q ∈ Subgroup.centralizer (Subgroup.zpowers f : Set X) := by
    have hmem : q ∈ Q ⊓ Subgroup.centralizer (Subgroup.zpowers f : Set X) := by
      rw [htop]; exact hq
    exact (Subgroup.mem_inf.mp hmem).2
  exact ((Subgroup.mem_centralizer_iff.mp hqC) f (Subgroup.mem_zpowers f)).symm

private lemma card_zwr_one : Nat.card (UC326.ZWr 1) = 81 := by
  simpa using (UC326.zwr_card_center_Zwr (n := 1) (by norm_num)).1

private lemma index_eq_three_of_card_eq_27 {Q : Subgroup (UC326.ZWr 1)}
    (hQ : Nat.card Q = 27) : Q.index = 3 := by
  have hmul := Subgroup.card_mul_index Q
  rw [hQ, card_zwr_one] at hmul
  have h81 : (81 : ℕ) = 27 * 3 := by norm_num
  rw [h81] at hmul
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) hmul

private lemma normal_of_card_eq_27 {Q : Subgroup (UC326.ZWr 1)}
    (hQ : Nat.card Q = 27) : Q.Normal := by
  apply Subgroup.normal_of_index_eq_minFac_card
  rw [index_eq_three_of_card_eq_27 hQ, card_zwr_one]
  norm_num

private lemma sup_zpowers_eq_top_of_not_mem {Q : Subgroup (UC326.ZWr 1)} {c : UC326.ZWr 1}
    (hQ : Nat.card Q = 27) (hcQ : c ∉ Q) : Q ⊔ Subgroup.zpowers c = ⊤ := by
  have hQindex := index_eq_three_of_card_eq_27 hQ
  have hlt : Q < Q ⊔ Subgroup.zpowers c := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    apply hcQ
    have hmem : c ∈ Q ⊔ Subgroup.zpowers c := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
    rwa [← heq] at hmem
  have hltidx := Subgroup.index_strictAnti hlt
  rw [hQindex] at hltidx
  have hdvd : (Q ⊔ Subgroup.zpowers c).index ∣ Q.index := Subgroup.index_dvd_of_le le_sup_left
  rw [hQindex] at hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact Subgroup.index_eq_one.mp h
  · omega

private lemma center_le_commutator_zwr :
    Subgroup.center (UC326.ZWr 1) ≤ commutator (UC326.ZWr 1) := by
  have hgen : UC326.el 1 1 1 1 (0 : ZMod 3) ∈ commutator (UC326.ZWr 1) := by
    have h := Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤)
      (g₁ := UC326.el 1 0 1 2 0) (g₂ := UC326.el 1 0 0 0 1) trivial trivial
    have heq : ⁅UC326.el 1 0 1 2 0, UC326.el 1 0 0 0 1⁆ =
        UC326.el 1 1 1 1 (0 : ZMod 3) := by
      rw [UC326.commutator_el_base_one 0 1 2 0 0 0]
      have h0 : (0 : ZMod 3) - 2 = 1 := by decide
      have h1 : (1 : ZMod 3) - 0 = 1 := by decide
      have h2 : (2 : ZMod 3) - 1 = 1 := by decide
      rw [h0, h1, h2]
    rwa [heq] at h
  have hdiag_le : UC326.diagSub 1 ≤ commutator (UC326.ZWr 1) := by
    have hg_mem : UC326.el 1 1 1 1 (0 : ZMod 3) ∈ UC326.diagSub 1 := by
      refine ⟨Multiplicative.ofAdd 1, ?_⟩
      rw [UC326.diagHom_apply, toAdd_ofAdd]
    have hg_ne : UC326.el 1 1 1 1 (0 : ZMod 3) ≠ 1 := by
      intro h
      have h0 := congrArg
        (fun w : UC326.ZWr 1 => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 0))) h
      simp [UC326.el] at h0
    have hord : orderOf (UC326.el 1 1 1 1 (0 : ZMod 3)) = 3 := by
      apply orderOf_eq_prime ?_ hg_ne
      rw [UC326.el_pow_base]
      have h3 : (3 : ZMod 3) = 0 := by decide
      simp [h3, UC326.el_zero_zero]
    have hcard : Nat.card (Subgroup.zpowers (UC326.el 1 1 1 1 (0 : ZMod 3))) = 3 := by
      rw [Nat.card_zpowers, hord]
    have hle : Subgroup.zpowers (UC326.el 1 1 1 1 (0 : ZMod 3)) ≤ UC326.diagSub 1 :=
      Subgroup.zpowers_le.mpr hg_mem
    have heq : UC326.diagSub 1 = Subgroup.zpowers (UC326.el 1 1 1 1 (0 : ZMod 3)) :=
      (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, UC326.card_diagSub]; norm_num)).symm
    rw [heq]
    exact Subgroup.zpowers_le.mpr hgen
  exact (UC326.center_eq_diag (n := 1) (by norm_num)).trans_le hdiag_le

private lemma commutator_le_of_card_eq_27 {Q : Subgroup (UC326.ZWr 1)} {c : UC326.ZWr 1}
    (hQ : Nat.card Q = 27) (hsup : Q ⊔ Subgroup.zpowers c = ⊤) :
    commutator (UC326.ZWr 1) ≤ Q := by
  haveI : Q.Normal := normal_of_card_eq_27 hQ
  haveI : IsMulCommutative ↥(Subgroup.zpowers c) := inferInstance
  exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance

private lemma mem_center_of_mem_centralizer {Q : Subgroup (UC326.ZWr 1)} {c : UC326.ZWr 1}
    (hQ : Nat.card Q = 27) (hcQ : c ∉ Q)
    (hc : c ∈ Subgroup.centralizer (Q : Set (UC326.ZWr 1))) :
    c ∈ Subgroup.center (UC326.ZWr 1) := by
  have hsup := sup_zpowers_eq_top_of_not_mem hQ hcQ
  rw [Subgroup.mem_center_iff]
  intro x
  have hx : x ∈ Subgroup.centralizer ({c} : Set (UC326.ZWr 1)) := by
    have htop : Subgroup.centralizer ({c} : Set (UC326.ZWr 1)) = ⊤ := by
      rw [eq_top_iff, ← hsup]
      refine sup_le ?_ ?_
      · intro q hq
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hc) q hq
      · intro z hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        exact (Commute.refl c).zpow_left n |>.eq
    rw [htop]
    exact Subgroup.mem_top x
  exact Subgroup.mem_centralizer_singleton_iff.mp hx

theorem centralizer_le_of_card_eq_27_zwr {Q : Subgroup (UC326.ZWr 1)}
    (hQ : Nat.card Q = 27) : Subgroup.centralizer (Q : Set (UC326.ZWr 1)) ≤ Q := by
  intro c hc
  by_contra hcQ
  have hcZ := mem_center_of_mem_centralizer hQ hcQ hc
  have hsup := sup_zpowers_eq_top_of_not_mem hQ hcQ
  exact hcQ ((center_le_commutator_zwr.trans (commutator_le_of_card_eq_27 hQ hsup)) hcZ)

private lemma sylow_inf_centralizer_le_of_card_eq_27 {X : Type*} [Group X] [Finite X]
    {S : Sylow 3 X} {Q C : Subgroup X} (e : ↥(S : Subgroup X) ≃* UC326.ZWr 1)
    (hQ : Nat.card Q = 27) (hQleS : Q ≤ (S : Subgroup X))
    (hC : C = Subgroup.centralizer (Q : Set X)) : (S : Subgroup X) ⊓ C ≤ Q := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro x hx
  obtain ⟨hxS, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxCQ : x ∈ Subgroup.centralizer (Q : Set X) := by rw [← hC]; exact hxC
  let QS : Subgroup ↥S := Q.subgroupOf (S : Subgroup X)
  have hQS_card : Nat.card ↥QS = 27 := by
    change Nat.card ↥(Q.subgroupOf (S : Subgroup X)) = 27
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleS).toEquiv]
    exact hQ
  have hxcent : (⟨x, hxS⟩ : ↥S) ∈ Subgroup.centralizer (QS : Set ↥S) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    apply Subtype.ext
    have hqQ : (q : X) ∈ Q := Subgroup.mem_subgroupOf.mp hq
    exact Subgroup.mem_centralizer_iff.mp hxCQ (q : X) hqQ
  let QZ : Subgroup (UC326.ZWr 1) := QS.map e.toMonoidHom
  have hQZ_card : Nat.card ↥QZ = 27 := by
    change Nat.card ↥(QS.map e.toMonoidHom) = 27
    exact (Subgroup.card_map_of_injective e.injective).trans hQS_card
  have hmap := CFSG.GorensteinWalter.centralizer_map_le_of_mulEquiv e QS
    (Subgroup.centralizer (QS : Set ↥S)) le_rfl
  have himg : e ⟨x, hxS⟩ ∈ QZ := by
    apply centralizer_le_of_card_eq_27_zwr hQZ_card
    exact hmap (Subgroup.mem_map_of_mem e.toMonoidHom hxcent)
  obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.mp himg
  have hqeq : q = (⟨x, hxS⟩ : ↥S) := e.injective hqe
  have hxQ' : (q : X) ∈ Q := Subgroup.mem_subgroupOf.mp hq
  rwa [hqeq] at hxQ'

private lemma isSylowOf_inf_of_normal {X : Type*} [Group X] [Finite X] {S : Sylow 3 X}
    {C : Subgroup X} (hCnormal : C.Normal) :
    CFSG.ABGLocalTools.IsSylowOf 3 ((S : Subgroup X) ⊓ C) C := by
  have hS_sylow_top : CFSG.ABGLocalTools.IsSylowOf 3 (S : Subgroup X) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, S.isPGroup', by simpa using S.not_dvd_index⟩
  exact CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hS_sylow_top le_top
    (by rw [Subgroup.normalizer_eq_top_iff.mpr hCnormal])

private lemma mem_center_of_mem_centralizer_subgroup {X : Type*} [Group X] {Q C : Subgroup X}
    (hC : C = Subgroup.centralizer (Q : Set X)) {x : ↥C} (hxQ : (x : X) ∈ Q) :
    x ∈ Subgroup.center C := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hy : (y : X) ∈ Subgroup.centralizer (Q : Set X) := by rw [← hC]; exact y.2
  exact (Subgroup.mem_centralizer_iff.mp hy (x : X) hxQ).symm

private lemma eq_inf_of_isSylowOf_inf_of_pPrimeCore_eq_bot {X : Type*} [Group X] [Finite X]
    (h3' : CFSG.pPrimeCore 3 X = ⊥) {C : Subgroup X} {S : Sylow 3 X}
    (hCnormal : C.Normal)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 ((S : Subgroup X) ⊓ C) C)
    (hcent : ∀ x : ↥C, (x : X) ∈ (S : Subgroup X) → x ∈ Subgroup.center C) :
    C = (S : Subgroup X) ⊓ C := by
  classical
  obtain ⟨P, hP⟩ := hP.exists_sylow_eq_subgroupOf
  have hPleZ : (P : Subgroup C) ≤ Subgroup.center C := by
    intro x hx
    rw [hP] at hx
    exact hcent x (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
  have hPcent : Subgroup.normalizer ((P : Subgroup C) : Set C) ≤
      Subgroup.centralizer ((P : Subgroup C) : Set C) := by
    have htop : Subgroup.centralizer ((P : Subgroup C) : Set C) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_center_iff.mp (hPleZ hy) x).symm
    rw [htop]
    exact le_top
  obtain ⟨K, hKnormal, hKnot3, hKidx, -, hKchar, hKcomp, hKsup, hKinf, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement P hPcent
  haveI : K.Characteristic := hKchar
  have hKle : (K.map C.subtype) ≤ CFSG.pPrimeCore 3 X := by
    refine le_sSup ⟨?_, ?_⟩
    · exact ConjAct.normal_of_characteristic_of_normal
    · rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).mpr hKnot3
  rw [h3'] at hKle
  have hKbot : K = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective K C.subtype_injective).mp (le_bot_iff.mp hKle)
  have hPtop : (P : Subgroup C) = ⊤ := by
    rw [hKbot] at hKsup
    simpa using hKsup
  have hle : C ≤ (S : Subgroup X) ⊓ C := by
    intro x hx
    have hxP : (⟨x, hx⟩ : ↥C) ∈ (P : Subgroup C) := by rw [hPtop]; trivial
    have hxSC : ((⟨x, hx⟩ : ↥C) : X) ∈ ((S : Subgroup X) ⊓ C) :=
      Subgroup.mem_subgroupOf.mp (hP ▸ hxP)
    simpa using hxSC
  exact le_antisymm hle inf_le_right

theorem not_five_dvd_card {X : Type} [Group X] [Finite X] (h3' : CFSG.pPrimeCore 3 X = ⊥)
    (S : Sylow 3 X) (e : ↥(S : Subgroup X) ≃* UC326.ZWr 1)
    (hO : Nat.card (CFSG.pCore 3 X) = 27) : ¬ 5 ∣ Nat.card X := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let Q : Subgroup X := CFSG.pCore 3 X
  have hQcard : Nat.card Q = 27 := hO
  have hQnormal : Q.Normal := CFSG.pCore_normal
  have hQleS : Q ≤ (S : Subgroup X) := CFSG.Glauberman.pCore_le_sylow S
  let C : Subgroup X := Subgroup.centralizer (Q : Set X)
  have hCnormal : C.Normal := by
    haveI : Q.Normal := hQnormal
    exact Subgroup.normal_centralizer
  have hSC : (S : Subgroup X) ⊓ C ≤ Q :=
    sylow_inf_centralizer_le_of_card_eq_27 e hQcard hQleS rfl
  have hP := isSylowOf_inf_of_normal (S := S) hCnormal
  have hcent : ∀ x : ↥C, (x : X) ∈ (S : Subgroup X) → x ∈ Subgroup.center C := by
    intro x hx
    exact mem_center_of_mem_centralizer_subgroup (Q := Q) (C := C) rfl
      (hSC (Subgroup.mem_inf.mpr ⟨hx, x.2⟩))
  have hCeq := eq_inf_of_isSylowOf_inf_of_pPrimeCore_eq_bot h3' hCnormal hP hcent
  have hC_le_Q : C ≤ Q := hCeq ▸ hSC
  intro h5dvd
  obtain ⟨f, hford⟩ := exists_prime_orderOf_dvd_card' (G := X) 5 h5dvd
  have hfnorm : f ∈ Subgroup.normalizer (Q : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hQnormal]
    exact Subgroup.mem_top f
  have hfcent : f ∈ C := mem_centralizer_of_orderOf_eq_five hQcard hford hfnorm
  have hfQ : f ∈ Q := hC_le_Q hfcent
  have hdvd : orderOf f ∣ Nat.card Q := Subgroup.orderOf_dvd_natCard Q hfQ
  rw [hford, hQcard] at hdvd
  norm_num at hdvd

private lemma le_relPPrimeCore_of_isSylowOf_inf {G : Type} [Group G] [Finite G]
    {M H : Subgroup G} (hq : ¬ 5 ∣ Nat.card (↥H ⧸ CFSG.pPrimeCore 3 ↥H))
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf 5 R (H ⊓ M)) :
    R ≤ CFSG.Open.relPPrimeCore 3 H := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hRleHM : R ≤ H ⊓ M := hR.le
  have hRleH : R ≤ H := hRleHM.trans inf_le_left
  have hR5 : IsPGroup 5 R := hR.isPGroup
  let OH : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  have hOHmap : OH.map H.subtype = CFSG.Open.relPPrimeCore 3 H :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      Nat.prime_three H).symm
  have hOHnormal : OH.Normal := CFSG.pPrimeCore_normal
  haveI : OH.Normal := hOHnormal
  have himg_triv : (R.subgroupOf H).map (QuotientGroup.mk' OH) = ⊥ := by
    have hRsub5 : IsPGroup 5 (R.subgroupOf H) := hR5.comap_subtype
    have himg5 : IsPGroup 5 ((R.subgroupOf H).map (QuotientGroup.mk' OH)) := hRsub5.map _
    obtain ⟨k, hk⟩ := himg5.exists_card_eq
    have hdvd : Nat.card ((R.subgroupOf H).map (QuotientGroup.mk' OH)) ∣
        Nat.card (↥H ⧸ OH) := Subgroup.card_subgroup_dvd_card _
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      exact hq ((dvd_pow_self 5 hk0).trans hdvd)
    have hk1 : Nat.card ((R.subgroupOf H).map (QuotientGroup.mk' OH)) = 1 := by
      rw [hk, hk0, pow_zero]
    exact Subgroup.card_eq_one.mp hk1
  have hRsubO : R.subgroupOf H ≤ OH := by
    intro x hx
    have hxmap : (QuotientGroup.mk' OH) x ∈ (R.subgroupOf H).map (QuotientGroup.mk' OH) :=
      Subgroup.mem_map_of_mem _ hx
    rw [himg_triv] at hxmap
    exact (QuotientGroup.eq_one_iff x).mp (by simpa using hxmap)
  intro r hr
  have hrH : r ∈ H := hRleH hr
  have hmem : (⟨r, hrH⟩ : ↥H) ∈ OH := hRsubO hr
  rw [← hOHmap]
  exact Subgroup.mem_map_of_mem H.subtype hmem

private lemma isSylowOf_relPPrimeCore_of_isSylowOf_inf {G : Type} [Group G] [Finite G]
    {M H : Subgroup G} (hq : ¬ 5 ∣ Nat.card (↥H ⧸ CFSG.pPrimeCore 3 ↥H))
    (hN : ∀ R : Subgroup G, IsPGroup 5 R → R ≠ ⊥ → R ≤ M →
      Subgroup.normalizer (R : Set G) ≤ M)
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf 5 R (H ⊓ M)) (hRne : R ≠ ⊥) :
    CFSG.ABGLocalTools.IsSylowOf 5 R (CFSG.Open.relPPrimeCore 3 H) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let O : Subgroup G := CFSG.Open.relPPrimeCore 3 H
  have hOleH : O ≤ H :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le H
  have hR5 : IsPGroup 5 R := hR.isPGroup
  have hRleHM : R ≤ H ⊓ M := hR.le
  have hRleM : R ≤ M := hRleHM.trans inf_le_right
  have hRleO : R ≤ O := le_relPPrimeCore_of_isSylowOf_inf hq hR
  have hRsyl_inf : CFSG.ABGLocalTools.IsSylowOf 5 R ((H ⊓ M) ⊓ O) :=
    CFSG.ABGLocalTools.IsSylowOf.of_le hR (fun x hx => ⟨hRleHM hx, hRleO hx⟩) inf_le_left
  refine CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le
    (T := R) (H := H ⊓ M) (M := O) hRsyl_inf ?_
  intro x hx
  obtain ⟨hxnorm, hxO⟩ := Subgroup.mem_inf.mp hx
  exact Subgroup.mem_inf.mpr ⟨hOleH hxO, hN R hR5 hRne hRleM hxnorm⟩

private lemma frattini_sup_eq_top {G : Type} [Group G] [Finite G] {H : Subgroup G}
    {OH : Subgroup ↥H} (hOHnormal : OH.Normal)
    (hOHmap : OH.map H.subtype = CFSG.Open.relPPrimeCore 3 H)
    {R : Subgroup G}
    (hRsyl : CFSG.ABGLocalTools.IsSylowOf 5 R (CFSG.Open.relPPrimeCore 3 H)) :
    Subgroup.normalizer ((R.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊔ OH = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hOleH : CFSG.Open.relPPrimeCore 3 H ≤ H :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le H
  have hRleH : R ≤ H := hRsyl.le.trans hOleH
  have hRsubH_map : (R.subgroupOf H).map H.subtype = R :=
    Subgroup.map_subgroupOf_eq_of_le hRleH
  haveI : OH.Normal := hOHnormal
  have hRsylOH : CFSG.ABGLocalTools.IsSylowOf 5 (R.subgroupOf H) OH := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (K := H)).mp ?_
    rw [hRsubH_map, hOHmap]
    exact hRsyl
  obtain ⟨P, hP⟩ := hRsylOH
  have h := Sylow.normalizer_sup_eq_top (N := OH) (P := P)
  rw [hP] at h
  exact h

private lemma le_sup_of_frattini {G : Type} [Group G] [Finite G] {M H : Subgroup G}
    (hN : ∀ R : Subgroup G, IsPGroup 5 R → R ≠ ⊥ → R ≤ M →
      Subgroup.normalizer (R : Set G) ≤ M)
    {OH : Subgroup ↥H} (hOHnormal : OH.Normal)
    (hOHmap : OH.map H.subtype = CFSG.Open.relPPrimeCore 3 H)
    {R : Subgroup G} (hR5 : IsPGroup 5 R) (hRne : R ≠ ⊥) (hRleM : R ≤ M) (hRleH : R ≤ H)
    (hfr : Subgroup.normalizer ((R.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊔ OH = ⊤) :
    H ≤ (H ⊓ M) ⊔ CFSG.Open.relPPrimeCore 3 H := by
  classical
  haveI : OH.Normal := hOHnormal
  intro x hx
  let h : ↥H := ⟨x, hx⟩
  have hmem : h ∈ Subgroup.normalizer ((R.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊔ OH := by
    rw [hfr]
    exact Subgroup.mem_top h
  obtain ⟨n, hn, o, ho, hno⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  have hnH : (n : G) ∈ H := n.2
  have hnM : (n : G) ∈ M := by
    have hnR : (n : G) ∈ Subgroup.normalizer (R : Set G) := by
      have h1 := Subgroup.mem_map_of_mem H.subtype hn
      have h2 := Subgroup.le_normalizer_map (H := R.subgroupOf H) H.subtype h1
      rwa [Subgroup.map_subgroupOf_eq_of_le hRleH] at h2
    exact hN R hR5 hRne hRleM hnR
  have hoO : (o : G) ∈ CFSG.Open.relPPrimeCore 3 H := by
    rw [← hOHmap]
    exact Subgroup.mem_map_of_mem H.subtype ho
  have hval : x = (n : G) * (o : G) := by
    have hconj := congrArg (fun y : ↥H => (y : G)) hno
    simpa using hconj.symm
  rw [hval]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hnH, hnM⟩) (Subgroup.mem_sup_right hoO)

theorem le_sup_relPPrimeCore_of_five {G : Type} [Group G] [Finite G] {M H : Subgroup G}
    (hN : ∀ R : Subgroup G, IsPGroup 5 R → R ≠ ⊥ → R ≤ M →
      Subgroup.normalizer (R : Set G) ≤ M)
    (h5 : 5 ∣ Nat.card (H ⊓ M : Subgroup G))
    (hq : ¬ 5 ∣ Nat.card (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) :
    H ≤ (H ⊓ M) ⊔ CFSG.Open.relPPrimeCore 3 H := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf (p := 5) (G := G) (H ⊓ M)
  have hRne : R ≠ ⊥ := by
    obtain ⟨Q, hQeq⟩ := hR.exists_sylow_eq_subgroupOf
    have hQne : (Q : Subgroup ↥(H ⊓ M)) ≠ ⊥ := Sylow.ne_bot_of_dvd_card (p := 5) Q h5
    intro hbot
    apply hQne
    rw [hQeq, hbot]
    simp
  let OH : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  have hOHnormal : OH.Normal := CFSG.pPrimeCore_normal
  have hOHmap : OH.map H.subtype = CFSG.Open.relPPrimeCore 3 H :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      Nat.prime_three H).symm
  have hRsylO := isSylowOf_relPPrimeCore_of_isSylowOf_inf hq hN hR hRne
  have hfr := frattini_sup_eq_top hOHnormal hOHmap hRsylO
  exact le_sup_of_frattini hN hOHnormal hOHmap hR.isPGroup hRne
    (hR.le.trans inf_le_right) (hR.le.trans inf_le_left) hfr

end A10Five

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D}

private lemma card_range_le_twentyfive (F : A10Frame c) {E : Subgroup G} (hE_le : E ≤ D.M)
    (hE : CFSG.Open.IsElemAbelian 5 E) :
    Nat.card ↥(((c.a10Hom F.iso).comp (Subgroup.inclusion hE_le)).range) ≤ 25 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let f : ↥E →* Equiv.Perm (Fin 10) := (c.a10Hom F.iso).comp (Subgroup.inclusion hE_le)
  change Nat.card ↥f.range ≤ 25
  have hf5 : IsPGroup 5 ↥f.range :=
    hE.isPGroup.of_surjective (f.codRestrict f.range fun x => ⟨x, rfl⟩) (by
      rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩)
  have hfA : f.range ≤ alternatingGroup (Fin 10) := by
    rintro y ⟨x, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    have hx5 : x ^ 5 = 1 := by
      apply Subtype.ext
      simpa using hE.2 x x.2
    have hy5 : (f x) ^ 5 = 1 := by rw [← map_pow, hx5, map_one]
    have hsign5 : (Equiv.Perm.sign (f x)) ^ 5 = 1 := by rw [← map_pow, hy5, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (f x)) with h | h
    · exact h
    · rw [h] at hsign5
      norm_num at hsign5
  let fa : Subgroup (alternatingGroup (Fin 10)) := f.range.subgroupOf _
  have hfa5 : IsPGroup 5 ↥fa := hf5.comap_subtype
  obtain ⟨S, hSle⟩ := hfa5.exists_le_sylow
  have hle : Nat.card ↥fa ≤ Nat.card ↥(S : Subgroup (alternatingGroup (Fin 10))) :=
    Subgroup.card_le_of_le hSle
  rw [CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen.card_sylow_five S] at hle
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hfA).toEquiv] at hle

private lemma five_dvd_card_ker_a10Hom (F : A10Frame c)
    (h5 : 3 ≤ CFSG.Open.pRank 5 D.M) : 5 ∣ Nat.card ((c.a10Hom F.iso).ker) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨E, hE_le, hE_ab, hE_card⟩ :=
    CFSG.SectionRank.exists_pRank (p := 5) (by norm_num) D.M
  have hE5 : IsPGroup 5 E := hE_ab.isPGroup
  have h125 : 125 ∣ Nat.card E := by
    rw [hE_card]
    exact pow_dvd_pow 5 h5
  let f : ↥E →* Equiv.Perm (Fin 10) := (c.a10Hom F.iso).comp (Subgroup.inclusion hE_le)
  have hrange_le : Nat.card ↥f.range ≤ 25 := card_range_le_twentyfive F hE_le hE_ab
  have hker5 : 5 ∣ Nat.card ↥f.ker := by
    by_contra hnot
    have hcop : Nat.Coprime 5 (Nat.card ↥f.ker) :=
      (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).mpr hnot
    have hcardEq := Subgroup.card_ker_mul_card_range f
    have h125' : 125 ∣ Nat.card ↥f.ker * Nat.card ↥f.range := by
      rw [hcardEq]
      exact h125
    have h125range : 125 ∣ Nat.card ↥f.range := (hcop.pow_left 3).dvd_of_dvd_mul_left h125'
    have hle := Nat.le_of_dvd (Nat.card_pos) h125range
    omega
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥f.ker) 5 hker5
  let k : (c.a10Hom F.iso).ker := ⟨⟨(x.1).1, hE_le (x.1).2⟩, by
    have hx1 : f (x : ↥E) = 1 := MonoidHom.mem_ker.mp x.2
    exact hx1⟩
  have hordk : orderOf k = 5 := by
    rw [← Subgroup.orderOf_coe k]
    have hkval : (k : ↥D.M) = Subgroup.inclusion hE_le ((x : ↥f.ker) : ↥E) :=
      Subtype.ext rfl
    rw [hkval, orderOf_injective (Subgroup.inclusion hE_le)
      (Subgroup.inclusion_injective hE_le) ((x : ↥f.ker) : ↥E)]
    rw [show orderOf ((x : ↥f.ker) : ↥E) = orderOf (x : ↥f.ker) from
      Subgroup.orderOf_coe (x : ↥f.ker)]
    exact hxord
  have hdvd : orderOf (k : ↥D.M) ∣ Nat.card ↥(c.a10Hom F.iso).ker :=
    Subgroup.orderOf_dvd_natCard (c.a10Hom F.iso).ker k.2
  rw [Subgroup.orderOf_coe k] at hdvd
  rw [hordk] at hdvd
  exact hdvd

private lemma five_dvd_card_of_sylow_five {K : Type*} [Group K] [Finite K] (R : Sylow 5 K)
    (hRne : (R : Subgroup K) ≠ ⊥) : 5 ∣ Nat.card ↥R := by
  obtain ⟨k, hk⟩ := R.isPGroup'.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hRne
    rw [pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  have hk' : Nat.card ↥R = 5 ^ k := hk
  rw [hk']
  exact dvd_pow_self 5 hk0

private lemma commutator_mem_L (F : A10Frame c) {K : Subgroup ↥D.M} {BM : Subgroup ↥D.M}
    {b : ↥BM} {r : ↥K} [MulDistribMulAction ↥BM ↥K]
    (hbL : ((b : ↥D.M) : G) ∈ c.L)
    (hsmul : ∀ (b : ↥BM) (r : ↥K),
      ((b • r : ↥K) : ↥D.M) = (b : ↥D.M) * (r : ↥D.M) * (b : ↥D.M)⁻¹) :
    (((r * (b • r)⁻¹ : ↥K)) : G) ∈ c.L := by
  have hrM : (((r : ↥K) : ↥D.M) : G) ∈ D.M := ((r : ↥K) : ↥D.M).2
  have hconjL : (((r : ↥K) : ↥D.M) : G) * ((b : ↥D.M) : G) *
      (((r : ↥K) : ↥D.M) : G)⁻¹ ∈ c.L :=
    (Subgroup.mem_normalizer_iff.mp (Ctx82E3.le_normalizer_L c hrM) _).mp hbL
  have hmul : (((r : ↥K) : ↥D.M) : G) * ((b : ↥D.M) : G) *
      (((r : ↥K) : ↥D.M) : G)⁻¹ * (((b : ↥D.M) : G))⁻¹ ∈ c.L :=
    c.L.mul_mem hconjL (c.L.inv_mem hbL)
  have hcoe : (((r * (b • r)⁻¹ : ↥K)) : G) =
      (((r : ↥K) : ↥D.M) : G) * ((b : ↥D.M) : G) *
        (((r : ↥K) : ↥D.M) : G)⁻¹ * (((b : ↥D.M) : G))⁻¹ := by
    have h1 : ((r * (b • r)⁻¹ : ↥K) : ↥D.M) =
        (r : ↥D.M) * ((b • r : ↥K) : ↥D.M)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
    have h3 : (((r * (b • r)⁻¹ : ↥K)) : G) =
        (((r : ↥K) : ↥D.M) : G) * ((((b • r : ↥K) : ↥D.M) : G))⁻¹ := by
      have := congrArg (fun z : ↥D.M => (z : G)) h1
      simpa using this
    have h4 : ((((b • r : ↥K) : ↥D.M) : G)) =
        ((b : ↥D.M) : G) * (((r : ↥K) : ↥D.M) : G) * ((b : ↥D.M) : G)⁻¹ :=
      congrArg (fun z : ↥D.M => (z : G)) (hsmul b r)
    rw [h3, h4]
    group
  rw [hcoe]
  exact hmul

private lemma commutator_mem_pCore (F : A10Frame c)
    (hker : ∀ x (hx : x ∈ c.L), c.a10Hom F.iso ⟨x, c.hyp81.1 hx⟩ = 1 →
      x ∈ (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype)
    {K : Subgroup ↥D.M} (hK : K = (c.a10Hom F.iso).ker) {BM : Subgroup ↥D.M}
    {b : ↥BM} {r : ↥K} [MulDistribMulAction ↥BM ↥K]
    (hbL : ((b : ↥D.M) : G) ∈ c.L)
    (hsmul : ∀ (b : ↥BM) (r : ↥K),
      ((b • r : ↥K) : ↥D.M) = (b : ↥D.M) * (r : ↥D.M) * (b : ↥D.M)⁻¹) :
    (((r * (b • r)⁻¹ : ↥K)) : G) ∈ (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype := by
  have hL := commutator_mem_L (F := F) (b := b) (r := r) hbL hsmul
  refine hker _ hL ?_
  have hMeq : (⟨(((r * (b • r)⁻¹ : ↥K)) : G), c.hyp81.1 hL⟩ : ↥D.M) =
      ((r * (b • r)⁻¹ : ↥K)) := Subtype.ext rfl
  rw [hMeq]
  have hmem : ((r * (b • r)⁻¹ : ↥K) : ↥D.M) ∈ (c.a10Hom F.iso).ker := by
    rw [← hK]
    exact (r * (b • r)⁻¹).2
  exact MonoidHom.mem_ker.mp hmem

private lemma commute_of_invariant_sylow (F : A10Frame c)
    (hker : ∀ x (hx : x ∈ c.L), c.a10Hom F.iso ⟨x, c.hyp81.1 hx⟩ = 1 →
      x ∈ (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype)
    {K : Subgroup ↥D.M} (hKnormal : K.Normal) (hK : K = (c.a10Hom F.iso).ker)
    {BM : Subgroup ↥D.M} {R : Sylow 5 ↥K} [MulDistribMulAction ↥BM ↥K]
    (hbL : ∀ b : ↥BM, ((b : ↥D.M) : G) ∈ c.L)
    (hsmul : ∀ (b : ↥BM) (r : ↥K),
      ((b • r : ↥K) : ↥D.M) = (b : ↥D.M) * (r : ↥D.M) * (b : ↥D.M)⁻¹)
    (hRinv : ∀ (b : ↥BM) (r : ↥K), r ∈ R → (b • r : ↥K) ∈ R)
    (hRG5 : IsPGroup 5 ((R : Subgroup ↥K).map (D.M.subtype.comp K.subtype)))
    {b : ↥BM} {r : ↥K} (hr : r ∈ R) :
    ((r : ↥K) : ↥D.M) * (b : ↥D.M) = (b : ↥D.M) * ((r : ↥K) : ↥D.M) := by
  classical
  haveI : K.Normal := hKnormal
  have hinv : (b • r) ∈ R := hRinv b r hr
  let cK : ↥K := r * (b • r)⁻¹
  have hcK_R : cK ∈ R := R.mul_mem hr (R.inv_mem hinv)
  have hcK_O2 : ((cK : ↥K) : G) ∈ (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype :=
    commutator_mem_pCore F hker hK (hbL b) hsmul
  have hcK_RG : ((cK : ↥K) : G) ∈ (R : Subgroup ↥K).map (D.M.subtype.comp K.subtype) :=
    Subgroup.mem_map.mpr ⟨cK, hcK_R, rfl⟩
  have hdisj : Disjoint ((R : Subgroup ↥K).map (D.M.subtype.comp K.subtype))
      ((CFSG.Open.pCore 2 ↥c.L).map c.L.subtype) :=
    IsPGroup.disjoint_of_ne 5 2 (by norm_num) _ _ hRG5
      (CFSG.pCore_isPGroup.map c.L.subtype)
  have hcK1G : ((cK : ↥K) : G) = 1 := by
    have hmem : ((cK : ↥K) : G) ∈ (R : Subgroup ↥K).map (D.M.subtype.comp K.subtype) ⊓
        (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype := ⟨hcK_RG, hcK_O2⟩
    rw [hdisj.eq_bot] at hmem
    simpa using hmem
  have hcK1 : cK = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hcK1G
  have hcK1' : r * (b • r)⁻¹ = 1 := hcK1
  have h1 : r = b • r := by
    calc r = r * (b • r)⁻¹ * (b • r) := by group
      _ = (b • r) := by rw [hcK1']; group
  have h2 : ((r : ↥K) : ↥D.M) = ((b • r : ↥K) : ↥D.M) :=
    congrArg (fun x : ↥K => ((x : ↥K) : ↥D.M)) h1
  have h3 : ((r : ↥K) : ↥D.M) =
      (b : ↥D.M) * ((r : ↥K) : ↥D.M) * (b : ↥D.M)⁻¹ := by
    calc ((r : ↥K) : ↥D.M) = ((b • r : ↥K) : ↥D.M) := h2
      _ = (b : ↥D.M) * ((r : ↥K) : ↥D.M) * (b : ↥D.M)⁻¹ := hsmul b r
  calc ((r : ↥K) : ↥D.M) * (b : ↥D.M) =
      ((b : ↥D.M) * ((r : ↥K) : ↥D.M) * (b : ↥D.M)⁻¹) * (b : ↥D.M) := by
        conv_lhs => rw [h3]
    _ = (b : ↥D.M) * ((r : ↥K) : ↥D.M) := by group

private lemma invariant_sylow_le_centralizer (F : A10Frame c)
    (hker : ∀ x (hx : x ∈ c.L), c.a10Hom F.iso ⟨x, c.hyp81.1 hx⟩ = 1 →
      x ∈ (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype)
    {K : Subgroup ↥D.M} (hKnormal : K.Normal) (hK : K = (c.a10Hom F.iso).ker)
    {B : Subgroup G} (hBL : B ≤ c.L)
    {BM : Subgroup ↥D.M} (hBM : BM = B.subgroupOf D.M) {R : Sylow 5 ↥K}
    [MulDistribMulAction ↥BM ↥K]
    (hbL : ∀ b : ↥BM, ((b : ↥D.M) : G) ∈ c.L)
    (hsmul : ∀ (b : ↥BM) (r : ↥K),
      ((b • r : ↥K) : ↥D.M) = (b : ↥D.M) * (r : ↥D.M) * (b : ↥D.M)⁻¹)
    (hRinv : ∀ (b : ↥BM) (r : ↥K), r ∈ R → (b • r : ↥K) ∈ R)
    (hRG5 : IsPGroup 5 ((R : Subgroup ↥K).map (D.M.subtype.comp K.subtype))) :
    ((R : Subgroup ↥K).map (D.M.subtype.comp K.subtype)) ≤
      Subgroup.centralizer (B : Set G) ⊓ D.M := by
  intro x hx
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbM : b ∈ D.M := hBL.trans c.hyp81.1 hb
    have hbBM : (⟨b, hbM⟩ : ↥D.M) ∈ BM := by
      rw [hBM]
      exact Subgroup.mem_subgroupOf.mpr hb
    exact (congrArg (fun z : ↥D.M => (z : G))
      (commute_of_invariant_sylow F hker hKnormal hK hbL hsmul hRinv hRG5
        (b := ⟨⟨b, hbM⟩, hbBM⟩) hr)).symm
  · exact ((r : ↥K) : ↥D.M).2

theorem five_dvd_card_centralizer_inf (F : A10Frame c)
    (hker : ∀ x (hx : x ∈ c.L), c.a10Hom F.iso ⟨x, c.hyp81.1 hx⟩ = 1 →
      x ∈ (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype)
    (h5 : 3 ≤ CFSG.Open.pRank 5 D.M) {B : Subgroup G} (hBL : B ≤ c.L) (hB : IsPGroup 3 B) :
    5 ∣ Nat.card (Subgroup.centralizer (B : Set G) ⊓ D.M : Subgroup G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let K : Subgroup ↥D.M := (c.a10Hom F.iso).ker
  have hKnormal : K.Normal := MonoidHom.normal_ker _
  have hK3' : Nat.Coprime (Nat.card K) 3 :=
    c.coprime_card_ker_a10Hom F.iso F.center (fun P hP => F.le_L_of_isSylowOf hP)
  have hKnot3 : ¬ 3 ∣ Nat.card K :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).mp hK3'.symm
  have hK5 : 5 ∣ Nat.card K := five_dvd_card_ker_a10Hom F h5
  let BM : Subgroup ↥D.M := B.subgroupOf D.M
  have hBM3 : IsPGroup 3 ↥BM := hB.comap_subtype
  have hbL : ∀ b : ↥BM, ((b : ↥D.M) : G) ∈ c.L :=
    fun b => hBL (Subgroup.mem_subgroupOf.mp b.2)
  haveI : K.Normal := hKnormal
  let φ : ↥BM →* MulAut ↥K := (MulAut.conjNormal (H := K)).comp BM.subtype
  letI : MulDistribMulAction ↥BM ↥K := MulDistribMulAction.compHom ↥K φ
  obtain ⟨R, hRinv⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.coprime_pgroup_exists_invariant_sylow
      (G := ↥K) (A := ↥BM) 3 5 hBM3 hKnot3
  have hsmul : ∀ (b : ↥BM) (r : ↥K),
      ((b • r : ↥K) : ↥D.M) = (b : ↥D.M) * ((r : ↥K) : ↥D.M) * (b : ↥D.M)⁻¹ := by
    intro b r
    change (((MulAut.conjNormal (H := K) (BM.subtype b)) r : ↥K) : ↥D.M) = _
    rw [MulAut.conjNormal_apply]
    rfl
  have hRG5 : IsPGroup 5 ((R : Subgroup ↥K).map (D.M.subtype.comp K.subtype)) :=
    R.isPGroup'.map _
  have hRGle := invariant_sylow_le_centralizer F hker hKnormal rfl hBL rfl hbL hsmul hRinv hRG5
  have hRne : (R : Subgroup ↥K) ≠ ⊥ := Sylow.ne_bot_of_dvd_card (p := 5) R hK5
  have hRcard5 : 5 ∣ Nat.card ↥R := five_dvd_card_of_sylow_five R hRne
  have hRGcard : Nat.card ((R : Subgroup ↥K).map (D.M.subtype.comp K.subtype)) =
      Nat.card ↥R :=
    Subgroup.card_map_of_injective (D.M.subtype_injective.comp K.subtype_injective)
  have hdvd : Nat.card ((R : Subgroup ↥K).map (D.M.subtype.comp K.subtype)) ∣
      Nat.card (Subgroup.centralizer (B : Set G) ⊓ D.M : Subgroup G) :=
    Subgroup.card_dvd_of_le hRGle
  rw [hRGcard] at hdvd
  exact hRcard5.trans hdvd

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
