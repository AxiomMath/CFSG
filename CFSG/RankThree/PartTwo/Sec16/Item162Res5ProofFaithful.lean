module

public import CFSG.RankThree.PartTwo.Sec16.Item162Res4ProofChoice
public import CFSG.RankThree.PartTwo.Sec16.Item162Res5ProofPerm
import CFSG.RankThree.PartTwo.Sec17.Item171GenProofA7
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

namespace Res162Five

variable {G : Type} [Group G] [Finite G]

noncomputable def permAutSeven : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
  MulEquiv.ofBijective MulAut.conjNormal
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num))

noncomputable def autToPerm {X : Type*} [Group X] (φ : X ≃* alternatingGroup (Fin 7)) :
    MulAut X →* Equiv.Perm (Fin 7) :=
  permAutSeven.symm.toMonoidHom.comp (MulAut.congr φ).toMonoidHom

theorem autToPerm_injective {X : Type*} [Group X] (φ : X ≃* alternatingGroup (Fin 7)) :
    Function.Injective (autToPerm φ) :=
  permAutSeven.symm.injective.comp (MulAut.congr φ).injective

theorem exists_eq_conj_of_mem_alternatingGroup {X : Type*} [Group X]
    (φ : X ≃* alternatingGroup (Fin 7)) {τ : MulAut X}
    (hτ : autToPerm φ τ ∈ alternatingGroup (Fin 7)) : ∃ x : X, τ = MulAut.conj x := by
  set σ := autToPerm φ τ with hσ
  have h1 : permAutSeven σ = MulAut.congr φ τ := by
    rw [hσ, autToPerm]
    exact permAutSeven.apply_symm_apply _
  have h2 : permAutSeven σ = MulAut.conj (⟨σ, hτ⟩ : alternatingGroup (Fin 7)) := by
    change MulAut.conjNormal ((⟨σ, hτ⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) = _
    exact MulAut.conjNormal_val
  refine ⟨φ.symm ⟨σ, hτ⟩, ?_⟩
  ext x
  have h3 := DFunLike.congr_fun (h1.symm.trans h2) (φ x)
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at h3
  rw [MulAut.conj_apply]
  apply φ.injective
  rw [h3, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem exists_inv_mul_mem_centralizer {L : Subgroup G}
    (hθ : aschbacherSolvableCore 3 ↥L = ⊥) {s : G} (hs : s ∈ Subgroup.normalizer (L : Set G))
    {x : ↥L ⧸ aschbacherSolvableCore 3 ↥L}
    (hx : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨s, hs⟩) = MulAut.conj x) :
    ∃ l ∈ L, l⁻¹ * s ∈ Subgroup.centralizer (L : Set G) := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨l, l.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have h1 := DFunLike.congr_fun hx ((⟨y, hy⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L)
  rw [Sec4.thetaQuotMulAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul, QuotientGroup.eq, hθ, Subgroup.mem_bot] at h1
  have h2 : (L.normalizerMonoidHom ⟨s, hs⟩ ⟨y, hy⟩ : ↥L) = l * ⟨y, hy⟩ * l⁻¹ :=
    inv_mul_eq_one.mp h1
  have h3 : s * y * s⁻¹ = (l : G) * y * (l : G)⁻¹ := by
    have := congrArg Subtype.val h2
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at this
    simpa using this
  calc y * ((l : G)⁻¹ * s) = (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * s := by group
    _ = (l : G)⁻¹ * (s * y * s⁻¹) * s := by rw [h3]
    _ = (l : G)⁻¹ * s * y := by group

theorem inf_centralizer_eq_bot {L : Subgroup G} (hθ : aschbacherSolvableCore 3 ↥L = ⊥)
    (φL : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) :
    L ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  obtain ⟨-, hZ, -, -, -⟩ := KFacts.KS14.a7_facts (↥L ⧸ aschbacherSolvableCore 3 ↥L) ⟨φL⟩
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzL, hzC⟩ := Subgroup.mem_inf.mp hz
  have hmk : ((⟨z, hzL⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC y y.2)
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff, hθ, Subgroup.mem_bot] at hmk
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmk)

theorem theta_eq_bot_of_seven {L Y : Subgroup G} (hLY : L ≤ Y)
    (φL : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) (hO : CFSG.Open.pCoreOf 2 L = ⊥) :
    aschbacherSolvableCore 3 ↥L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  intro t ht
  have h1 : (t : G) ∈ CFSG.Open.pCoreOf 2 Y := Res162b.theta_le_pCoreOf_of_seven hLY φL φ t ht
  have hle : L ⊓ CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2 L := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
    · exact (le_inf Subgroup.le_normalizer
        (hLY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y).to_le inf_le_right
  have h2 : (t : G) ∈ CFSG.Open.pCoreOf 2 L := hle ⟨t.2, h1⟩
  rw [hO, Subgroup.mem_bot] at h2
  exact Subgroup.mem_bot.mpr (Subtype.ext h2)

theorem exists_inv_mul_mem_centralizer_of_le {A : Subgroup G} {c : G} {L : Subgroup G}
    (hD : Sec13Data G A c L)
    (φL : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))
    (hθ : aschbacherSolvableCore 3 ↥L = ⊥) {Sc : Subgroup G} (hSc2 : IsPGroup 2 Sc)
    (hAS : A ≤ Subgroup.normalizer (Sc : Set G)) (hSL : Sc ≤ Subgroup.normalizer (L : Set G))
    {s : G} (hs : s ∈ Sc) : ∃ l ∈ L, l⁻¹ * s ∈ Subgroup.centralizer (L : Set G) := by
  classical
  set N := Subgroup.normalizer (L : Set G) with hN
  set ρ : N →* Equiv.Perm (Fin 7) :=
    (autToPerm φL).comp ((Sec4.thetaQuotMulAut ↥L).comp L.normalizerMonoidHom) with hρ
  set E := (Sec4.autThetaQuot A L).map (autToPerm φL) with hE
  set P := (Sec4.autThetaQuot Sc L).map (autToPerm φL) with hP
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective (autToPerm_injective φL)]
    exact Sec17.Proof171Gen.card_autThetaQuot_eq_nine hD
  have hP2 : IsPGroup 2 P := by
    have h1 : IsPGroup 2 ((Sc ⊓ N).subgroupOf N) :=
      (hSc2.to_le inf_le_left).comap_of_injective N.subtype N.subtype_injective
    exact ((h1.map L.normalizerMonoidHom).map (Sec4.thetaQuotMulAut ↥L)).map (autToPerm φL)
  have hEP : E ≤ Subgroup.normalizer (P : Set (Equiv.Perm (Fin 7))) := by
    intro e he
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp he
    obtain ⟨a, haN, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
    refine Subgroup.mem_normalizer_fintype fun p hp => ?_
    obtain ⟨τ', hτ', rfl⟩ := Subgroup.mem_map.mp hp
    obtain ⟨t, htN, htS, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ'
    have hatN : a * t * a⁻¹ ∈ N := mul_mem (mul_mem haN htN) (inv_mem haN)
    have hatS : a * t * a⁻¹ ∈ Sc := (Subgroup.mem_normalizer_iff.mp (hAS haA) t).mp htS
    refine Subgroup.mem_map.mpr ⟨_, Sec4.mem_autThetaQuot_iff.mpr ⟨a * t * a⁻¹, hatN, hatS, rfl⟩,
      ?_⟩
    have heq : (⟨a * t * a⁻¹, hatN⟩ : N) = ⟨a, haN⟩ * ⟨t, htN⟩ * (⟨a, haN⟩ : N)⁻¹ := rfl
    change ρ ⟨a * t * a⁻¹, hatN⟩ = ρ ⟨a, haN⟩ * ρ ⟨t, htN⟩ * (ρ ⟨a, haN⟩)⁻¹
    rw [heq, map_mul, map_mul, map_inv]
  have hPA := le_alternatingGroup_of_le_normalizer hP2 hE9 hEP
  have hsP : autToPerm φL (Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨s, hSL hs⟩)) ∈ P :=
    Subgroup.mem_map_of_mem _ (Sec4.mem_autThetaQuot_iff.mpr ⟨s, hSL hs, hs, rfl⟩)
  obtain ⟨x, hx⟩ := exists_eq_conj_of_mem_alternatingGroup φL (hPA hsP)
  exact exists_inv_mul_mem_centralizer hθ (hSL hs) hx

theorem le_of_faithful {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h142 : Concl142 A (lB A))
    (φL : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))
    (hO : CFSG.Open.pCoreOf 2 L = ⊥) {Y : Subgroup G} (hLY : L ≤ Y)
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) {Sc : Subgroup G}
    (hSc : Sc ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G))
      (piOf 2))
    (hQ : Sc ⊓ Subgroup.centralizer (L : Set G) = ⊥) : Sc ≤ L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set C := Subgroup.centralizer (L : Set G) with hC
  have hθ := theta_eq_bot_of_seven hLY φL φ hO
  have hZ := inf_centralizer_eq_bot hθ φL
  have hSc2 : IsPGroup 2 Sc := isPGroup_of_mem_scriptQPi Nat.prime_two hSc.prop
  have hAS : A ≤ Subgroup.normalizer (Sc : Set G) := hSc.prop.1.1.1.2.2
  have hScH : Sc ≤ H := hSc.prop.1.2
  have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
    normalizer_zpowers_le_normalizer_L h (three_dvd_card_of_mem_lA h h.zpowers_mem_omegaA
      h.mem_lA)
  have hSL : Sc ≤ Subgroup.normalizer (L : Set G) := hScH.trans hHL
  have hLH : L ≤ H := hD.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c)
  have hNC := Res162d.normalizer_le_normalizer_centralizer' L
  set R := C ⊓ (Sc ⊔ L) with hR
  have hR2 : IsPGroup 2 R := by
    intro r
    have hrS : (r : G) ∈ ((Sc ⊔ L : Subgroup G) : Set G) := (Subgroup.mem_inf.mp r.2).2
    have hrC : (r : G) ∈ C := (Subgroup.mem_inf.mp r.2).1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Sc L hSL] at hrS
    obtain ⟨s, hs, l, hl, hsl⟩ := hrS
    obtain ⟨k, hk⟩ := hSc2 ⟨s, hs⟩
    have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcomm : Commute (r : G) l⁻¹ :=
      (show Commute (r : G) l from (Subgroup.mem_centralizer_iff.mp hrC l hl).symm).inv_right
    have hs' : s = (r : G) * l⁻¹ := by rw [← hsl]; group
    have h1 : (r : G) ^ 2 ^ k = l ^ 2 ^ k := by
      rw [hs', hcomm.mul_pow, inv_pow, mul_inv_eq_one] at hk'
      exact hk'
    have h2 : (r : G) ^ 2 ^ k ∈ L ⊓ C := ⟨h1 ▸ pow_mem hl _, pow_mem hrC _⟩
    rw [hZ, Subgroup.mem_bot] at h2
    exact ⟨k, Subtype.ext (by simpa using h2)⟩
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    (le_inf (hD.le_normalizer.trans hNC) (le_normalizer_sup hAS hD.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hSR : Sc ≤ Subgroup.normalizer (R : Set G) :=
    (le_inf (hSL.trans hNC) (le_normalizer_sup Subgroup.le_normalizer hSL)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  set T := Sc ⊔ R with hT
  have hT2 : IsPGroup 2 T := IsPGroup.to_sup_of_normal_right' hSc2 hR2 hSR
  have hTH : T ≤ H := sup_le hScH (inf_le_right.trans (sup_le hScH hLH))
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := le_normalizer_sup hAS hAR
  have hT3 : ¬ 3 ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hTQ : T ∈ scriptQ A (lB A) := mem_scriptQ_of_concl142 h142 h.zpowers_mem_omegaA
    ⟨hTH, (isPiSubgroup_piCompl_iff Nat.prime_three T).mpr hT3, hAT⟩
  have hTmem : T ∈ scriptQPi A (lB A) H (piOf 2) :=
    ⟨⟨hTQ, hTH⟩, (isPiSubgroup_piOf_iff Nat.prime_two T).mpr hT2⟩
  have hTS : T ≤ Sc := hSc.2 hTmem le_sup_left
  have hR1 : R = ⊥ := by
    rw [eq_bot_iff, ← hQ]
    exact le_inf (le_sup_right.trans hTS) inf_le_left
  intro s hs
  obtain ⟨l, hl, hls⟩ := exists_inv_mul_mem_centralizer_of_le hD φL hθ hSc2 hAS hSL hs
  have hz : l⁻¹ * s ∈ R :=
    ⟨hls, mul_mem (Subgroup.mem_sup_right (inv_mem hl)) (Subgroup.mem_sup_left hs)⟩
  rw [hR1, Subgroup.mem_bot, inv_mul_eq_one] at hz
  exact hz ▸ hl

end Res162Five

theorem step162ChoiceFaithful_of (h142 : Concl142R) : Step162ChoiceFaithful := by
  intro G _ _ A c L h h7 hO Y hY hLY hY7 Sc hSc hQ
  obtain ⟨φL⟩ := h7
  obtain ⟨φ⟩ := hY7
  exact ⟨Y, hY, hLY, ((Res162Five.le_of_faithful h (h142 G A c L h) φL hO hLY φ hSc hQ).trans
    hLY).trans Subgroup.le_normalizer⟩

end CFSG.RankThree.PartTwo.Sec16
