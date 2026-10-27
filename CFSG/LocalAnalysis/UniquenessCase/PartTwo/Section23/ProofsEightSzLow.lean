module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightSzLowK
public import CFSG.LocalAnalysis.UniquenessCase.UC6R2
import CFSG.LocalAnalysis.UniquenessCase.UC22P20yd
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
import CFSG.GroupTheory.WielandtProductBasic
import CFSG.GroupTheory.Commutator.SubgroupOf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsOmegaMinus)

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_inf_of_mem_calC {S L K : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ L) L) (hK : K ∈ calC L) :
    CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ K) K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have aux : ∀ {A B : Subgroup G}, CFSG.Open.IsSubnormal A B →
      CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ B) B →
      CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ A) A := by
    intro A B h
    induction h with
    | refl => exact id
    | step hle hnorm _ ih =>
        intro hB
        have hM := ih hB
        have hN := (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 hnorm
        have := hM.inf_of_le_normalizer hle hN
        rwa [inf_assoc, inf_eq_right.mpr hle] at this
  exact aux hK.1 hS

theorem mem_normalizer_of_mem_calLOf {T M H L : Subgroup G}
    (hL : L ∈ calLOf T M H) (hTH : T ≤ H) {y : G}
    (hy : ∀ K ∈ calC H, y ∈ Subgroup.normalizer (K : Set G)) :
    y ∈ Subgroup.normalizer (L : Set G) := by
  obtain ⟨hLcal, hLsub⟩ := hL
  obtain ⟨hTL, -, -, K, hK, hLjoin⟩ := hLcal
  have hKH : K ∈ calC H := ⟨hK.1.trans hLsub, hK.2.1, hK.2.2⟩
  have hmem : ∀ t : T, K.map (MulAut.conj (t : G)).toMonoidHom ∈ calC H := by
    intro t
    have hLmap : L.map (MulAut.conj (t : G)).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hTL t.2)
    have hKt : K.map (MulAut.conj (t : G)).toMonoidHom ∈ calC L :=
      UC6S846.calC_map L (MulAut.conj (t : G)) hLmap hK
    exact ⟨hKt.1.trans hLsub, hKt.2.1, hKt.2.2⟩
  rw [hLjoin, Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
  exact iSup_congr fun t => Subgroup.mem_normalizer_iff_map_conj_eq.mp (hy _ (hmem t))

private theorem ind_sylowBar_of_mem_normalizer (D : Data G) {L : Subgroup G}
    (hL : L ∈ calL D.T D.M) {t : G} (ht : t ∈ Subgroup.normalizer (L : Set G))
    (htT : t ∈ Subgroup.normalizer (D.T : Set G)) (x : Bar2 L) :
    x ∈ uc22p20iSylowBar D L ↔ uc22p20uInd L t ht x ∈ uc22p20iSylowBar D L := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) x
  have hN : t ∈ Subgroup.normalizer ((D.T ⊓ L : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨htT, ht⟩)
  have e : uc22p20uInd L t ht (QuotientGroup.mk' (CFSG.pCore 2 ↥L) l) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥L)
        ⟨t * (l : G) * t⁻¹, (Subgroup.mem_normalizer_iff.1 ht (l : G)).1 l.2⟩ := rfl
  rw [e, uc22p20i_mem_sylowBar_iff D hL, uc22p20i_mem_sylowBar_iff D hL]
  simpa using (Subgroup.mem_normalizer_iff.1 hN (l : G))

private theorem exists_sylowBar_invariant_of_odd (hKD : KDiag) (D : Data G) (h1930 : H1930 D)
    (h20_7 : S20_7 D) {L P : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hP : MinTInvParabolic D.T D.M L P) {y : G}
    (hy : Odd (orderOf y)) (hyT : y ∈ Subgroup.normalizer (D.T : Set G))
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) :
    ∃ Sbar : Sylow 2 (Bar2 L),
      (Sbar : Subgroup (Bar2 L)) = uc22p20iSylowBar D L ∧
      (∀ x ∈ (Sbar : Subgroup (Bar2 L)),
        uc22p20uInd L y hyL x ∈ (Sbar : Subgroup (Bar2 L))) ∧
      (Sbar : Subgroup (Bar2 L)) ≤ normalizer
        (((P.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) : Set (Bar2 L)) ∧
      ∀ x ∈ ((P.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))),
        uc22p20uInd L y hyL x ∈
          ((P.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let θ : MulAut (Bar2 L) := uc22p20uInd L y hyL
  let Pbar : Subgroup (Bar2 L) := (P.subgroupOf L).map π
  have hPbar : IsParabolicTwo (Bar2 L) Pbar := hP.1.1.2.2
  have hShape : Shape207 (Bar2 L) := shape207_of_s20_7 h20_7 h1930 hL
  have hθodd : Odd (orderOf θ) := by
    have hdvd : orderOf θ ∣
        orderOf (⟨y, hyL⟩ : ↥(Subgroup.normalizer (L : Set G))) := by
      change orderOf (uc22pwIndHom L (Subgroup.normalizer (L : Set G)) le_rfl ⟨y, hyL⟩) ∣
        orderOf (⟨y, hyL⟩ : ↥(Subgroup.normalizer (L : Set G)))
      exact orderOf_map_dvd _ _
    rw [← Subgroup.orderOf_coe] at hdvd
    exact Odd.of_dvd_nat hy hdvd
  let Sbar : Sylow 2 (Bar2 L) :=
    (uc22p20i_sylowBar_isPGroup D).toSylow (uc22p20i_sylowBar_index D hL)
  have hSbarCoe : (Sbar : Subgroup (Bar2 L)) = uc22p20iSylowBar D L :=
    IsPGroup.toSylow_coe _ _
  have hSbarInv : ∀ x ∈ (Sbar : Subgroup (Bar2 L)), θ x ∈ (Sbar : Subgroup (Bar2 L)) := by
    intro x hx
    rw [hSbarCoe] at hx ⊢
    exact (ind_sylowBar_of_mem_normalizer D hL hyL hyT x).1 hx
  have hSle : (Sbar : Subgroup (Bar2 L)) ≤ normalizer (Pbar : Set (Bar2 L)) := by
    rw [hSbarCoe]
    have h := CFSG.GroupTheory.map_subgroupOf_le_normalizer (M := L) (B := D.T) (X := P) π
      hP.1.2.1
    have hEq : D.T.subgroupOf L = (D.T ⊓ L).subgroupOf L := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [hEq] at h
    exact h
  have hPinv : ∀ x ∈ Pbar, θ x ∈ Pbar :=
    hKD (Bar2 L) hShape θ hθodd Sbar hSbarInv Pbar hPbar hSle
  refine ⟨Sbar, hSbarCoe, ?_, ?_, ?_⟩
  · simpa [θ] using hSbarInv
  · simpa [Pbar, π] using hSle
  · simpa [Pbar, π, θ] using hPinv

theorem mem_normalizer_hinf_of_kDiag (hKD : KDiag) (D : Data G) (h1930 : H1930 D)
    (h20_7 : S20_7 D) {L P : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hP : MinTInvParabolic D.T D.M L P) {y : G}
    (hy : Odd (orderOf y)) (hyT : y ∈ Subgroup.normalizer (D.T : Set G))
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) :
    y ∈ Subgroup.normalizer (Hinf P : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let Pbar : Subgroup (Bar2 L) := (P.subgroupOf L).map π
  obtain ⟨_, _, _, _, hPinv⟩ :=
    exists_sylowBar_invariant_of_odd hKD D h1930 h20_7 hL hP hy hyT hyL
  have hPinv' : ∀ x ∈ Pbar, uc22p20uInd L y hyL x ∈ Pbar := by
    simpa [Pbar, π] using hPinv
  have hpre : ∀ x : G, ∀ hx : x ∈ L, (π ⟨x, hx⟩ ∈ Pbar ↔ x ∈ P) := by
    intro x hx
    constructor
    · intro hxbar
      obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp hxbar
      have hpP : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
      have hk : p⁻¹ * (⟨x, hx⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq).1 hpx
      have hkP : ((p⁻¹ * (⟨x, hx⟩ : ↥L) : ↥L) : G) ∈ P :=
        hP.1.1.1 ⟨_, hk, rfl⟩
      have e : x = (p : G) * ((p⁻¹ * (⟨x, hx⟩ : ↥L) : ↥L) : G) := by
        simp
      rw [e]
      exact P.mul_mem hpP hkP
    · intro hxP
      exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.mpr hxP, rfl⟩
  have hyP : y ∈ Subgroup.normalizer (P : Set G) := by
    refine CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem (fun p hp => ?_)
    have hpL : p ∈ L := hP.1.1.2.1 hp
    have hLmem : y * p * y⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 hyL p).1 hpL
    have hpi : π ⟨y * p * y⁻¹, hLmem⟩ =
        uc22p20uInd L y hyL (π ⟨p, hpL⟩) := by
      change QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨y * p * y⁻¹, hLmem⟩ =
        uc22p20uInd L y hyL (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨p, hpL⟩)
      rw [show uc22p20uInd L y hyL (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨p, hpL⟩) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨y * p * y⁻¹, hLmem⟩ from rfl]
    have hθmem : uc22p20uInd L y hyL (π ⟨p, hpL⟩) ∈ Pbar := hPinv' _ (by
      rw [show π ⟨p, hpL⟩ ∈ Pbar ↔ p ∈ P from hpre p hpL]
      exact hp)
    rw [← hpi] at hθmem
    exact (hpre (y * p * y⁻¹) hLmem).1 hθmem
  simpa [Hinf, CFSG.inSubgroup] using
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := P) (K := CFSG.perfectResidual P) hyP

theorem exists_calLLow_le_calLOf_normalizer (D : Data G) (h1930 : H1930 D) (hR : UC6.R6_40_2 D)
    (h20_4 : S20_4 D) (h20_9 : S20_9 D) :
    ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ D.T ∧
      Subgroup.normalizer (D.T : Set G) ≤ Subgroup.normalizer (C : Set G) ∧
      ∃ L' ∈ calLOf D.T D.M (Subgroup.normalizer (C : Set G)),
        ∃ L₁ ∈ calLLow D.T D.M, L₁ ≤ L' ∧
          ∃ P : Subgroup G, MinTInvParabolic D.T D.M L' P ∧ L₁ = Hinf P := by
  classical
  have hMtop : D.M ≠ ⊤ := uc22p20a_M_ne_top D
  have hex : ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ D.T ∧ (C.subgroupOf D.T).Characteristic ∧
      ¬ Subgroup.normalizer (C : Set G) ≤ D.M := by
    by_contra h
    have hle : UC6.calCGS D.T ≤ D.M := by
      unfold UC6.calCGS
      refine iSup_le fun C => iSup_le fun hCne => iSup_le fun hCT => iSup_le fun hCchar => ?_
      by_contra hCNM
      exact h ⟨C, hCne, hCT, hCchar, hCNM⟩
    rw [hR.1] at hle
    exact hMtop (top_le_iff.mp hle)
  obtain ⟨C, hCne, hCT, hCchar, hCNM⟩ := hex
  have hCeq : (C.subgroupOf D.T).map D.T.subtype = C := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCT]
  have hNC : Subgroup.normalizer (D.T : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    haveI : (C.subgroupOf D.T).Characteristic := hCchar
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := D.T) (K := C.subgroupOf D.T)
    simpa [hCeq] using h
  have hH0 : Subgroup.normalizer (C : Set G) ∈ hSet D.T D.M := by
    refine ⟨Subgroup.le_normalizer.trans hNC, hCNM, ?_⟩
    have hloc : IsTwoLocal (Subgroup.normalizer (C : Set G)) :=
      ⟨C, hCne, D.sylowM.isPGroup.to_le hCT, rfl⟩
    exact D.standing.charTwo _ hloc
  obtain ⟨L', hL'⟩ := uc22p20s_calLOf_nonempty D h20_4 h1930 hH0
  obtain ⟨L₁, hL₁le, hmin⟩ :=
    Finite.exists_le_minimal
      (p := fun K : Subgroup G => K ∈ calL D.T D.M ∧ K ≤ L') (a := L')
      ⟨hL'.1, le_rfl⟩
  have hL₁cal : L₁ ∈ calL D.T D.M := hmin.prop.1
  have hL₁low : L₁ ∈ calLLow D.T D.M := by
    refine ⟨hL₁cal, ?_⟩
    intro K hKcal hKle
    exact ((minimal_iff.mp hmin).2 ⟨hKcal, hKle.trans hL₁le⟩ hKle).le
  obtain ⟨P, hP, hPeq⟩ := (h20_9 h1930 L' hL'.1 L₁).1 ⟨hL₁low, hL₁le⟩
  exact ⟨C, hCne, hCT, hNC, L', hL', L₁, hL₁low, hL₁le, P, hP, hPeq⟩

private theorem conj_mem_pCoreOf {L : Subgroup G} {b x : G} (hb : b ∈ L)
    (hx : x ∈ CFSG.Open.pCoreOf 2 L) :
    b * x * b⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  obtain ⟨x', hx', rfl⟩ := hx
  exact ⟨⟨b, hb⟩ * x' * ⟨b, hb⟩⁻¹, CFSG.pCore_normal.conj_mem x' hx' ⟨b, hb⟩, rfl⟩

private theorem mem_pCore_of_mem_pCoreOf {L : Subgroup G} {x : L}
    (hx : (x : G) ∈ CFSG.Open.pCoreOf 2 L) : x ∈ CFSG.pCore 2 L := by
  obtain ⟨y, hy, hyx⟩ := hx
  rw [Subtype.ext hyx] at hy
  exact hy

private theorem commutator_mem_pCoreOf_of_ind_eq_one {L : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hθ : uc22p20uInd L x hx = 1) {b : G} (hb : b ∈ L) :
    b * x * b⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  have h1 : uc22p20uInd L x hx (QuotientGroup.mk ⟨b, hb⟩) = QuotientGroup.mk ⟨b, hb⟩ := by
    rw [hθ]
    rfl
  rw [uc22p20uInd_mk] at h1
  have h2 : (⟨x * b * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx b).1 hb⟩ : ↥L)⁻¹ *
      ⟨b, hb⟩ ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq).1 h1
  have h4 : x * b⁻¹ * x⁻¹ * b ∈ CFSG.Open.pCoreOf 2 L :=
    ⟨_, h2, by simp [mul_assoc]⟩
  have h5 : (x * b⁻¹ * x⁻¹ * b)⁻¹ ∈ CFSG.Open.pCoreOf 2 L := inv_mem h4
  have h6 : b⁻¹ * x * b * x⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
    convert h5 using 1 <;> group
  have h7 : b * (b⁻¹ * x * b * x⁻¹) * b⁻¹ ∈ CFSG.Open.pCoreOf 2 L :=
    conj_mem_pCoreOf hb h6
  have e : b * (b⁻¹ * x * b * x⁻¹) * b⁻¹ = (b * x * b⁻¹ * x⁻¹)⁻¹ := by group
  rw [e] at h7
  simpa using inv_mem h7

private theorem ind_eq_one_of_commutator_mem_pCoreOf {L : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G))
    (h : ∀ b ∈ L, b * x * b⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 L) :
    uc22p20uInd L x hx = 1 := by
  ext q
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
  rw [uc22p20uInd_mk, MulAut.one_apply]
  apply (QuotientGroup.eq (s := CFSG.pCore 2 ↥L)).2
  apply mem_pCore_of_mem_pCoreOf
  have hc : (b : ↥L)⁻¹ * ((b : ↥L) * x * (b : ↥L)⁻¹ * x⁻¹) * (b : ↥L) ∈
      CFSG.Open.pCoreOf 2 L := by
    simpa using conj_mem_pCoreOf (L.inv_mem b.2) (h (b : G) b.2)
  convert hc using 1 <;> simp [mul_assoc]

theorem commutator_mem_pCoreOf_zpowers {L : Subgroup G} {y : G}
    (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (h : ∀ b ∈ L, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 L) :
    ∀ x ∈ Subgroup.zpowers y, ∀ b ∈ L,
      b * x * b⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  intro x hx b hb
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := Subgroup.zpowers_le.mpr hyL hx
  have hy1 : uc22pwIndHom L (Subgroup.normalizer (L : Set G)) le_rfl ⟨y, hyL⟩ = 1 := by
    change uc22p20uInd L y hyL = 1
    exact ind_eq_one_of_commutator_mem_pCoreOf hyL h
  have hx1 : uc22pwIndHom L (Subgroup.normalizer (L : Set G)) le_rfl ⟨x, hxN⟩ = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hsub : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        (⟨y, hyL⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ k := by
      ext
      simpa [hk]
    rw [hsub, map_zpow, hy1, one_zpow]
  change uc22p20uInd L x hxN = 1 at hx1
  exact commutator_mem_pCoreOf_of_ind_eq_one hxN hx1 hb

private theorem exists_commutator_mem_pCoreOf_subgroup {L : Subgroup G} {y : G}
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) :
    ∃ A : Subgroup G, A ≤ L ∧ ∀ b : G, b ∈ A ↔
      b ∈ L ∧ b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  let A : Subgroup G :=
    { carrier := {b | b ∈ L ∧ b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 L}
      one_mem' := ⟨L.one_mem, by simp⟩
      mul_mem' := by
        rintro b₁ b₂ ⟨hb₁, h₁⟩ ⟨hb₂, h₂⟩
        refine ⟨L.mul_mem hb₁ hb₂, ?_⟩
        have h₁' : b₁ * (b₂ * y * b₂⁻¹ * y⁻¹) * b₁⁻¹ ∈ CFSG.Open.pCoreOf 2 L :=
          conj_mem_pCoreOf hb₁ h₂
        have e : (b₁ * b₂) * y * (b₁ * b₂)⁻¹ * y⁻¹ =
            b₁ * (b₂ * y * b₂⁻¹ * y⁻¹) * b₁⁻¹ * (b₁ * y * b₁⁻¹ * y⁻¹) := by
          group
        rw [e]
        exact mul_mem h₁' h₁
      inv_mem' := by
        rintro b ⟨hb, hb'⟩
        refine ⟨L.inv_mem hb, ?_⟩
        have hc : b⁻¹ * (b * y * b⁻¹ * y⁻¹) * b ∈ CFSG.Open.pCoreOf 2 L := by
          simpa using conj_mem_pCoreOf (L.inv_mem hb) hb'
        have e : b⁻¹ * (b * y * b⁻¹ * y⁻¹) * b = (b⁻¹ * y * b * y⁻¹)⁻¹ := by
          group
        rw [e] at hc
        simpa using inv_mem hc }
  refine ⟨A, fun b hb => hb.1, fun b => Iff.rfl⟩

theorem commutator_mem_pCoreOf_sup {L L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ calC L)
    (h₂ : L₂ ∈ calC L) (hL : L = L₁ ⊔ L₂) {y : G}
    (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hy₁ : ∀ b ∈ L₁, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 L₁)
    (hy₂ : ∀ b ∈ L₂, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 L₂) :
    ∀ b ∈ L, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hAL, hA⟩ := exists_commutator_mem_pCoreOf_subgroup hyL
  have h₁A : L₁ ≤ A := by
    intro b hb
    rw [hA b]
    refine ⟨h₁.1.le hb, ?_⟩
    exact CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_subnormal 2 h₁.1
      (hy₁ b hb)
  have h₂A : L₂ ≤ A := by
    intro b hb
    rw [hA b]
    refine ⟨h₂.1.le hb, ?_⟩
    exact CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_subnormal 2 h₂.1
      (hy₂ b hb)
  have hLA : L ≤ A := by
    rw [hL]
    exact sup_le h₁A h₂A
  intro b hb
  exact (hA b).1 (hLA hb) |>.2

theorem commutator_mem_pCoreOf_of_kOrdBorel (hKO : KOrdBorel) {L S : Subgroup G} {m r : ℕ}
    (hm : 2 ≤ m) (hX : IsSz (Bar2 L) m ∨ IsL2 (Bar2 L) m ∨ IsSU3 (Bar2 L) m ∨ IsSL3 (Bar2 L) m ∨
      IsSp4 (Bar2 L) m ∨ IsOmegaMinus (Bar2 L) 4 m)
    (hr : r.Prime) (hr3 : 3 < r) (hrm : ¬ r ∣ m) (hr2m : ¬ r ∣ 2 ^ (2 * m) - 1)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S L) {y : G} (hyr : y ^ r = 1)
    (hyS : y ∈ Subgroup.normalizer (S : Set G))
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) :
    ∀ b ∈ L, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Syl, hSyl⟩ := hS.exists_sylow_eq_subgroupOf
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let Q : Sylow 2 (Bar2 L) := Sylow.mapSurjective (QuotientGroup.mk'_surjective _) Syl
  have hQcoe : (Q : Subgroup (Bar2 L)) = (S.subgroupOf L).map π := by
    change (Syl : Subgroup ↥L).map π = (S.subgroupOf L).map π
    rw [hSyl]
  have hQinv : ∀ x ∈ (Q : Subgroup (Bar2 L)),
      uc22p20uInd L y hyL x ∈ (Q : Subgroup (Bar2 L)) := by
    intro x hx
    rw [hQcoe] at hx ⊢
    obtain ⟨s, hs, hxs⟩ := Subgroup.mem_map.mp hx
    rw [← hxs]
    change uc22p20uInd L y hyL (QuotientGroup.mk s) ∈ (S.subgroupOf L).map π
    rw [uc22p20uInd_mk]
    have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
    have hLmem : y * (s : G) * y⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 hyL (s : G)).1 s.2
    have hSmem : y * (s : G) * y⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.1 hyS (s : G)).1 hsS
    exact Subgroup.mem_map.mpr ⟨⟨y * (s : G) * y⁻¹, hLmem⟩,
      Subgroup.mem_subgroupOf.mpr hSmem, rfl⟩
  have hθr : (uc22p20uInd L y hyL) ^ r = 1 := by
    have hpow : (⟨y, hyL⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ r = 1 := by
      ext
      simp [hyr]
    have h := map_pow (uc22pwIndHom L (Subgroup.normalizer (L : Set G)) le_rfl)
      (⟨y, hyL⟩ : ↥(Subgroup.normalizer (L : Set G))) r
    rw [hpow, map_one] at h
    change (uc22pwIndHom L (Subgroup.normalizer (L : Set G)) le_rfl ⟨y, hyL⟩) ^ r = 1
    exact h.symm
  have hθ1 : uc22p20uInd L y hyL = 1 :=
    hKO (Bar2 L) m hm hX r hr hr3 hrm hr2m Q (uc22p20uInd L y hyL) hθr hQinv
  intro b hb
  exact commutator_mem_pCoreOf_of_ind_eq_one hyL hθ1 hb

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
