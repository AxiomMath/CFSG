module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res3ProofCaseOneX
public import CFSG.RankThree.PartTwo.Sec20.Item20ResProofLCentral
import CFSG.RankThree.PartTwo.Sec18.Components
public import CFSG.RankThree.PartTwo.Sec20.Item20Res3ProofCaseOneCoords
public import CFSG.RankThree.PartTwo.Sec20.Item20Res3ProofSchur

public section

namespace CFSG.RankThree.PartTwo.Sec20.Res3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec20
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.CGT.T75N
open CFSG.RankThree.PartTwo.Sec20.Res2
open CFSG.Assembly.RankThreeEven (projSL)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_normalized {K : Type*} [Group K] [Finite K] {p : ℕ} (r : ℕ) [Fact p.Prime]
    [Fact r.Prime] {W E : Subgroup K} (hE : IsPGroup p E)
    (hEW : E ≤ Subgroup.normalizer (W : Set K)) (hW : ¬ p ∣ Nat.card W) :
    ∃ T : Sylow r W, ∀ g ∈ E, ∀ y ∈ (T : Subgroup W).map W.subtype,
      g * y * g⁻¹ ∈ (T : Subgroup W).map W.subtype := by
  classical
  let φ : E →* MulAut W := (Subgroup.normalizerMonoidHom W).comp (Subgroup.inclusion hEW)
  let _inst : MulDistribMulAction E W := MulDistribMulAction.compHom W φ
  have hcard : ¬ p ∣ Nat.card (Sylow r W) := by
    intro h
    apply hW
    obtain P : Sylow r W := default
    exact h.trans ((Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card _))
  obtain ⟨P, hP⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card (Sylow r W) hcard
  refine ⟨P, fun g hg y hy => ?_⟩
  obtain ⟨x, hxP, rfl⟩ := Subgroup.mem_map.mp hy
  have h1 : (⟨g, hg⟩ : E) • P = P := hP ⟨g, hg⟩
  have h2 : ((⟨g, hg⟩ : E) • x : W) ∈ ((⟨g, hg⟩ : E) • (P : Subgroup W)) :=
    Subgroup.smul_mem_pointwise_smul x _ _ hxP
  have h3 : ((⟨g, hg⟩ : E) • (P : Subgroup W)) = (P : Subgroup W) := by
    rw [← Sylow.pointwise_smul_def, h1]
  rw [h3] at h2
  exact ⟨_, h2, rfl⟩

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_prime {p : ℕ} [hp : Fact p.Prime] {y : G} (h : y ^ p = 1) :
    IsPGroup p (Subgroup.zpowers y) := by
  have hd : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one h
  rcases (Nat.dvd_prime hp.out).mp hd with h1 | h1
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])

omit [Finite G] in
theorem card_sup_zpowers_le {Y : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (Y : Set G)) [Finite Y] [Finite (Subgroup.zpowers c)] :
    Nat.card ↥(Y ⊔ Subgroup.zpowers c) ≤ Nat.card Y * Nat.card (Subgroup.zpowers c) := by
  have hle : Subgroup.zpowers c ≤ Subgroup.normalizer (Y : Set G) :=
    Subgroup.zpowers_le.mpr hc
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left Y (Subgroup.zpowers c) hle
  let f : ↥Y × ↥(Subgroup.zpowers c) → ↥(Y ⊔ Subgroup.zpowers c) := fun p =>
    ⟨(p.1 : G) * p.2, by
      rw [← SetLike.mem_coe, hset]
      exact Set.mul_mem_mul p.1.2 p.2.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rw [← SetLike.mem_coe, hset] at hx
    obtain ⟨u, hu, z, hz, rfl⟩ := hx
    exact ⟨(⟨u, hu⟩, ⟨z, hz⟩), rfl⟩
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_surjective f hf

section Fix

variable {K Q : Subgroup G} {F : Type} [Field F] [Finite F]
  {α : ↥K →* SpecialLinearGroup (Fin 3) F}

omit [Finite G] [Finite F] in
theorem eq_smul_e0_of_fix [CharP F 2] {v : SpecialLinearGroup (Fin 3) F} (hv : v ∈ vstab F)
    (hv3 : v ^ 3 = 1) (hv1 : v ≠ 1) {x : Fin 3 → F}
    (hx : (v : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x) : x 1 = 0 ∧ x 2 = 0 := by
  have hvu := not_mem_urad_of_pow_three hv3 hv1
  obtain ⟨e1, e2⟩ := mulVec_one_two_of_mem_vstab hv x
  by_contra hne
  apply blkSL_ne_one_of_not_mem_urad hv hvu
  refine sl2_eq_one_of_fix (blkSL_pow_three hv hv3) (x := ![x 1, x 2]) ?_ ?_
  · intro h
    apply hne
    exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
  · show blkMat (v : Matrix (Fin 3) (Fin 3) F) *ᵥ ![x 1, x 2] = ![x 1, x 2]
    have h1 := congrFun hx 1
    have h2 := congrFun hx 2
    rw [e1] at h1
    rw [e2] at h2
    ext i
    fin_cases i
    · simp [blkMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h1]
    · simp [blkMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h2]

omit [Finite G] in
theorem card_inf_centralizer_le_two (hF : Nat.card F = 2)
    (β : ↥Q →* Multiplicative (Fin 3 → F)) (hβinj : Function.Injective β)
    (hβ : ∀ (a : ↥K) (u v : ↥Q), (v : G) = a * u * (a : G)⁻¹ →
      Multiplicative.toAdd (β v) = (α a : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u))
    {d : ↥K} (hd : α d ∈ vstab F) (hd3 : α d ^ 3 = 1) (hd1 : α d ≠ 1) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer {(d : G)}) ≤ 2 := by
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hF, pow_one])
  let f : ↥(Q ⊓ Subgroup.centralizer {(d : G)}) → F := fun w =>
    Multiplicative.toAdd (β ⟨w, w.2.1⟩) 0
  have hfix : ∀ w : ↥(Q ⊓ Subgroup.centralizer {(d : G)}),
      (α d : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β ⟨w, w.2.1⟩) =
        Multiplicative.toAdd (β ⟨w, w.2.1⟩) := by
    intro w
    have hc : (d : G) * w * (d : G)⁻¹ = w := by
      rw [Subgroup.mem_centralizer_iff.mp w.2.2 (d : G) rfl]
      group
    exact (hβ d ⟨w, w.2.1⟩ ⟨w, w.2.1⟩ hc.symm).symm
  have hf : Function.Injective f := by
    intro w w' h
    have e : ∀ w : ↥(Q ⊓ Subgroup.centralizer {(d : G)}),
        Multiplicative.toAdd (β ⟨w, w.2.1⟩) =
          (Multiplicative.toAdd (β ⟨w, w.2.1⟩) 0) • (Pi.single 0 1 : Fin 3 → F) := fun w => by
      obtain ⟨h1, h2⟩ := eq_smul_e0_of_fix hd hd3 hd1 (hfix w)
      exact eq_smul_e0 h1 h2
    have : β ⟨w, w.2.1⟩ = β ⟨w', w'.2.1⟩ := by
      apply Multiplicative.toAdd.injective
      rw [e w, e w']
      change f w • _ = f w' • _
      rw [h]
    have h' := congrArg Subtype.val (hβinj this)
    exact Subtype.ext h'
  calc Nat.card ↥(Q ⊓ Subgroup.centralizer {(d : G)}) ≤ Nat.card F :=
        Nat.card_le_card_of_injective f hf
    _ = 2 := hF

theorem card_pCoreOf_inf_centralizer_le_four (hF : Nat.card F = 2)
    (β : ↥Q →* Multiplicative (Fin 3 → F)) (hβinj : Function.Injective β)
    (hβ : ∀ (a : ↥K) (u v : ↥Q), (v : G) = a * u * (a : G)⁻¹ →
      Multiplicative.toAdd (β v) = (α a : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u))
    (hQO : Q ≤ CFSG.Open.pCoreOf 2 K)
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 K) ≤ 2 * Nat.card Q)
    {d : ↥K} (hd : α d ∈ vstab F) (hd3 : α d ^ 3 = 1) (hd1 : α d ≠ 1) :
    Nat.card ↥(CFSG.Open.pCoreOf 2 K ⊓ Subgroup.centralizer {(d : G)}) ≤ 4 := by
  set O := CFSG.Open.pCoreOf 2 K with hO
  set C' := O ⊓ Subgroup.centralizer {(d : G)} with hC'
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hOQ := Subgroup.relIndex_mul_card (H := Q) (K := O)
  rw [inf_eq_left.mpr hQO] at hOQ
  have hidx : Q.relIndex O ≤ 2 := by
    by_contra hlt
    have : 3 * Nat.card Q ≤ Q.relIndex O * Nat.card Q := Nat.mul_le_mul_right _ (by omega)
    omega
  have hne : Q.relIndex O ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hOQ
    exact (Nat.card_pos (α := O)).ne' hOQ.symm
  have hidx' : Q.relIndex C' ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right inf_le_left hne).trans hidx
  have hQC : Nat.card ↥(Q ⊓ C') ≤ 2 := by
    have hle : Q ⊓ C' ≤ Q ⊓ Subgroup.centralizer {(d : G)} := inf_le_inf_left _ inf_le_right
    exact (Subgroup.card_le_of_le hle).trans
      (card_inf_centralizer_le_two hF β hβinj hβ hd hd3 hd1)
  have h := Subgroup.relIndex_mul_card (H := Q) (K := C')
  rw [← h]
  calc Q.relIndex C' * Nat.card ↥(Q ⊓ C') ≤ 2 * 2 := Nat.mul_le_mul hidx' hQC
    _ = 4 := by norm_num

end Fix

section Seven

theorem le_centralizer_of_pow_seven_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hNL : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hO2L : CFSG.Open.pCoreOf 2 L ≤ M) (hTN : T ≤ N)
    (h207 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (he : Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃* projSL 3 (GaloisField 2 1)))
    (hKN : ¬ kTwenty M c ≤ N)
    (hi : CFSG.Quasithin.IsC134Case 1 (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c))
    {y : G} (hyL : y ∈ L) (hy7 : y ^ 7 = 1) :
    CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) ≤
      Subgroup.centralizer {y} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨F, _, _, α, β, hF, hαs, hαk, hβinj, hβs, hβ, hN⟩ :=
    caseOne_coords_core hT hTN h207 he hKN hi
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hF, pow_one])
  obtain ⟨⟨hshort, -⟩, -⟩ := hi
  have hKM : kTwenty M c ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hMK : M ≤ Subgroup.normalizer (kTwenty M c : Set G) := le_normalizer_normalClosureIn M c
  have hKTK : kTwenty M c ⊔ T ≤ Subgroup.normalizer (kTwenty M c : Set G) :=
    sup_le Subgroup.le_normalizer (hT.sylow.le.trans hMK)
  have hQK : CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) ≤ kTwenty M c := by
    rw [CFSG.Quasithin.c134Q, Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKTK)
  have hKQ : kTwenty M c ≤ Subgroup.normalizer
      ((CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) : Subgroup G) : Set G) :=
    le_normalizer_commutator_right _ _
  have hQO : CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) ≤
      CFSG.Open.pCoreOf 2 (kTwenty M c) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQK hKQ
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le c134Q_le)
  have hOO : CFSG.Open.pCoreOf 2 (kTwenty M c) ≤ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left)
      (hKTK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hcomm : ⁅CFSG.Open.pCoreOf 2 (kTwenty M c), kTwenty M c⁆ ≤
      CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) :=
    Subgroup.commutator_mono hOO le_rfl
  have hTM : T ≤ M := hT.sylow.le
  have hQT : CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ≤ T :=
    pCoreOf_le_of_isSylowOf (hT.sylow.of_le le_sup_right (sup_le hKM hTM))
  have hQN : CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) ≤ N :=
    c134Q_le.trans (hQT.trans hTN)
  have : Group.IsPerfect ↥(kTwenty M c) := isPerfect_of_sl3 hshort.1 α hαs hαk
  have hOcard := card_pCoreOf_le_two_mul hF α hαs hαk hQK hKQ hQO hcomm
  have hQcard : Nat.card (CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c)) = 8 := by
    rw [Nat.card_congr (MulEquiv.ofBijective β ⟨hβinj, hβs⟩).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, hF]
    norm_num
  have hcA : c ∈ A := mem_of_hyp201 hT.toHyp201
  have hc3 : c ^ 3 = 1 := hT.mem_partTwoE.1.2 c hcA
  have hcK : c ∈ kTwenty M c := self_mem_normalClosureIn M c
  have hcN : c ∈ N := by
    rw [hNL]
    exact hAL hcA
  have hc1 : c ≠ 1 := by
    rintro rfl
    have hbot : kTwenty M (1 : G) = ⊥ := by
      rw [eq_bot_iff, kTwenty, normalClosureIn, Subgroup.closure_le]
      rintro _ ⟨m, -, rfl⟩
      rw [mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    have hcard1 : Nat.card ↥(kTwenty M (1 : G)) = 1 := by
      rw [hbot]
      exact Subgroup.card_bot
    have h1 : Nat.card (SpecialLinearGroup (Fin 3) F) ≤ 1 := by
      calc Nat.card (SpecialLinearGroup (Fin 3) F) ≤ Nat.card ↥(kTwenty M (1 : G)) :=
            Nat.card_le_card_of_surjective α hαs
        _ = 1 := hcard1
    have h2 : Nat.card (urad F) ≤ Nat.card (SpecialLinearGroup (Fin 3) F) :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    rw [card_urad, hF] at h2
    omega
  set X := normalClosureIn (kTwenty M c ⊓ N) c with hX
  set Y := CFSG.Open.pCoreOf 2 X with hY
  have hXK : X ≤ kTwenty M c := (normalClosureIn_le_inf hcK hcN).trans inf_le_left
  have hY2 : IsPGroup 2 Y := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hQX : CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) ≤ X :=
    le_X_of_natural hF hαs hαk hN hcK hcN hc3 hc1 hQK hQN hKQ β hβinj hβs hβ
  have hQY : CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) ≤ Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQX (hXK.trans hKQ)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le c134Q_le)
  have hYcard : Nat.card Y ≤ 64 := by
    have h : Nat.card Y ≤ 4 * Nat.card (CFSG.Open.pCoreOf 2 (kTwenty M c)) :=
      card_pCoreOf_X_le hF hαs hαk hN hcK hcN hc3 hc1
    rw [hQcard] at hOcard
    omega
  have hcX : c ∈ X := self_mem_normalClosureIn _ c
  have hXY : X ≤ Subgroup.normalizer (Y : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hq : Nat.card F % 3 = 2 := by rw [hF]
  have hαker : α.ker = (CFSG.Open.pCoreOf 2 (kTwenty M c)).subgroupOf (kTwenty M c) := by
    ext k
    rw [MonoidHom.mem_ker, hαk, Subgroup.mem_subgroupOf]
  have hyX : y ∈ Subgroup.normalizer (X : Set G) :=
    le_normalizer_X_core hT hNL hAL hO2L hTN hq α hαker
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hyL
  have hyc : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ Y :=
    commutator_mem_pCoreOf_normalClosureIn_core hT hNL hAL hyL hyX
  have hyY : y ∈ Subgroup.normalizer (Y : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X hyX
  set W := Y ⊔ Subgroup.zpowers c with hW
  have hWX : W ≤ X := sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
    (Subgroup.zpowers_le.mpr hcX)
  have hyW : Subgroup.zpowers y ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.zpowers_le]
    apply mem_normalizer_of_map_conj_le
    rw [hW, Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · rw [map_conj_eq_of_mem_normalizer hyY]
      exact le_sup_left
    · rw [Subgroup.zpowers_le]
      have h1 := hyc c hcX
      have : (MulAut.conj y).toMonoidHom c = (y * c * y⁻¹ * c⁻¹) * c := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [this]
      exact W.mul_mem (Subgroup.mem_sup_left h1)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  have hc_ord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hW7 : ¬ 7 ∣ Nat.card W := by
    have hcY : c ∈ Subgroup.normalizer (Y : Set G) := hXY hcX
    have hle := card_sup_zpowers_le hcY
    rw [Nat.card_zpowers, hc_ord] at hle
    have hYW : Nat.card Y ∣ Nat.card W := Subgroup.card_dvd_of_le le_sup_left
    obtain ⟨m, hm⟩ := hYW
    obtain ⟨a, ha⟩ := hY2.exists_card_eq
    intro h7
    rw [hm, ha] at h7
    have h7m : 7 ∣ m := (Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.Coprime.pow_right a (by norm_num)) h7)
    have hpos : 0 < Nat.card Y := Nat.card_pos
    have hm3 : m ≤ 3 := by
      rw [hm] at hle
      exact Nat.le_of_mul_le_mul_left hle hpos
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      exact (Nat.card_pos (α := W)).ne' hm
    obtain ⟨j, rfl⟩ := h7m
    omega
  have hW3 : 3 ∣ Nat.card W := by
    have h := orderOf_dvd_natCard (⟨c, Subgroup.mem_sup_right (Subgroup.mem_zpowers c)⟩ : W)
    rwa [Subgroup.orderOf_mk, hc_ord] at h
  have hPy : IsPGroup 7 (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_prime hy7
  obtain ⟨P3, hP3⟩ := exists_sylow_normalized 3 hPy hyW hW7
  obtain ⟨d₀, hd₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P3 : Subgroup W)) 3
    (P3.dvd_card_of_dvd_card hW3)
  set d : G := ((d₀ : W) : G) with hd
  have hdW : d ∈ W := (d₀ : W).2
  have hdX : d ∈ X := hWX hdW
  have hdP : d ∈ (P3 : Subgroup W).map W.subtype := ⟨d₀, d₀.2, rfl⟩
  have hd3 : d ^ 3 = 1 := by
    have h := pow_orderOf_eq_one d₀
    rw [hd₀] at h
    have := congrArg (fun x : ↥(P3 : Subgroup W) => ((x : W) : G)) h
    simpa using this
  have hd1 : d ≠ 1 := by
    intro h
    have : d₀ = 1 := Subtype.ext (Subtype.ext h)
    rw [this, orderOf_one] at hd₀
    exact absurd hd₀ (by norm_num)
  have hdy : y * d = d * y := by
    have hP3' : IsPGroup 3 ((P3 : Subgroup W).map W.subtype) := P3.isPGroup'.map _
    have hdisj := IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ hP3' hY2
    have h1 : y * d * y⁻¹ * d⁻¹ ∈ (P3 : Subgroup W).map W.subtype :=
      Subgroup.mul_mem _ (hP3 y (Subgroup.mem_zpowers y) d hdP) (Subgroup.inv_mem _ hdP)
    have h2 : y * d * y⁻¹ * d⁻¹ ∈ Y := hyc d hdX
    have h3 : y * d * y⁻¹ * d⁻¹ = 1 := by
      have := Subgroup.disjoint_def.mp hdisj h1 h2
      exact this
    calc y * d = (y * d * y⁻¹ * d⁻¹) * d * y := by group
      _ = d * y := by rw [h3, one_mul]
  have hdY : d ∈ Subgroup.normalizer (Y : Set G) := hXY hdX
  set σ := Y.normalizerMonoidHom ⟨y, hyY⟩ with hσ
  set τ := Y.normalizerMonoidHom ⟨d, hdY⟩ with hτ
  have hσ7 : σ ^ 7 = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨y, hyY⟩ : Subgroup.normalizer (Y : Set G)) ^ 7 = 1 :=
      Subtype.ext (by simpa using hy7)
    rw [this, map_one]
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτ, ← map_pow]
    have : (⟨d, hdY⟩ : Subgroup.normalizer (Y : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hd3)
    rw [this, map_one]
  have hστ : σ * τ = τ * σ := by
    rw [hσ, hτ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hdy
  have hdK : d ∈ kTwenty M c := hXK hdX
  have hdN : d ∈ N := ((normalClosureIn_le_inf hcK hcN) hdX).2
  obtain ⟨hαd, hαd3, hαd1⟩ := alpha_c_props hαk hN hdK hdN hd3 hd1
  have hfixO : ∀ w : ↥Y, τ w = w → (w : G) ∈ CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
      (w : G) ∈ Subgroup.centralizer {d} := by
    intro w hw
    have hwd : d * w * d⁻¹ = w := by
      have := congrArg Subtype.val hw
      rw [hτ, Sec4.normalizerMonoidHom_apply_coe] at this
      exact this
    have hwK : (w : G) ∈ kTwenty M c := (CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXK w.2
    have hwu : α ⟨w, hwK⟩ ∈ urad F :=
      map_pCoreOf_X_le_urad hF hαs hαk hN hcK hcN hc3 hc1
        ⟨⟨w, hwK⟩, Subgroup.mem_subgroupOf.mpr w.2, rfl⟩
    have hcomm' : α ⟨w, hwK⟩ * α ⟨d, hdK⟩ = α ⟨d, hdK⟩ * α ⟨w, hwK⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (w : G) * d = d * w
      calc (w : G) * d = (d * w * d⁻¹) * d := by rw [hwd]
        _ = d * w := by group
    have h1 := eq_one_of_mem_urad_of_commute hF hαd hαd3 hαd1 hwu hcomm'
    refine ⟨(hαk _).mp h1, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    rw [Set.mem_singleton_iff.mp hg]
    calc d * (w : G) = (d * w * d⁻¹) * d := by group
      _ = w * d := by rw [hwd]
  have hfix4 : Nat.card {w : ↥Y // τ w = w} ≤ 4 := by
    let f : {w : ↥Y // τ w = w} →
        ↥(CFSG.Open.pCoreOf 2 (kTwenty M c) ⊓ Subgroup.centralizer {d}) :=
      fun w => ⟨w.1, (hfixO w.1 w.2).1, (hfixO w.1 w.2).2⟩
    have hf : Function.Injective f := fun w w' h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    exact (Nat.card_le_card_of_injective f hf).trans
      (card_pCoreOf_inf_centralizer_le_four (d := ⟨d, hdK⟩) hF β hβinj hβ hQO hOcard
        hαd hαd3 hαd1)
  obtain ⟨q₀, hq₀⟩ := hβs (Multiplicative.ofAdd (Pi.single 0 1))
  have hq₀Y : (q₀ : G) ∈ Y := hQY q₀.2
  have hq₀1 : (⟨q₀, hq₀Y⟩ : ↥Y) ≠ 1 := by
    intro h
    have h'' : (q₀ : G) = 1 := congrArg Subtype.val h
    have h' : q₀ = 1 := Subtype.ext h''
    rw [h', map_one] at hq₀
    have := congrFun (congrArg Multiplicative.toAdd hq₀) 0
    simp at this
  have hτq₀ : τ ⟨q₀, hq₀Y⟩ = ⟨q₀, hq₀Y⟩ := by
    have hdq : d * q₀ * d⁻¹ ∈ CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) :=
      (Subgroup.mem_normalizer_iff.mp (hKQ hdK) _).mp q₀.2
    have hβd := hβ ⟨d, hdK⟩ q₀ ⟨_, hdq⟩ rfl
    rw [hq₀, toAdd_ofAdd] at hβd
    have hfixe : (α ⟨d, hdK⟩ : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 := hαd
    rw [hfixe, ← toAdd_ofAdd (Pi.single 0 1 : Fin 3 → F), ← hq₀] at hβd
    have hq : (⟨_, hdq⟩ : ↥(CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c))) = q₀ :=
      hβinj (Multiplicative.toAdd.injective hβd)
    apply Subtype.ext
    rw [hτ, Sec4.normalizerMonoidHom_apply_coe]
    exact congrArg Subtype.val hq
  have hσ1 := eq_one_of_commute_seven_three (hY2 : IsPGroup 2 ↥Y) hYcard hσ7 hτ3 hστ hfix4
    hq₀1 hτq₀
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff.mp hg]
  have h := congrArg (fun φ : MulAut ↥Y => ((φ ⟨q, hQY hq⟩ : ↥Y) : G)) hσ1
  simp only [hσ, Sec4.normalizerMonoidHom_apply_coe, MulAut.one_apply] at h
  calc y * q = (y * q * y⁻¹) * y := by group
    _ = q * y := by rw [h]

end Seven

section Main

theorem false_of_caseOne_L32_core {A M L N : Subgroup G} {c : G}
    {T : Subgroup G} (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hLq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* projSL 3 (GaloisField 2 2)))
    (hLp : ⁅L, L⁆ = L) (hLM : ¬ L ≤ M) (hO2L : CFSG.Open.pCoreOf 2 L ≤ M) (hTN : T ≤ N)
    (h204 : scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G) = {M})
    (h207 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (he : Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃* projSL 3 (GaloisField 2 1)))
    (hKN : ¬ kTwenty M c ≤ N)
    (hi : CFSG.Quasithin.IsC134Case 1 (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) with hQdef
  obtain ⟨e⟩ := hLq
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
    have := isSimpleGroup_projSL_three_galois_four
    exact e.isSimpleGroup
  have hrL : 7 ∣ Nat.card L := by
    rw [card_eq_of_nonempty_quotient e]
    exact (by norm_num : 7 ∣ 20160).mul_right _
  have hgen := closure_pow_eq_one_eq hLp hs (by decide : Nat.Prime 7) (by norm_num) hrL
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := by
    rw [← hgen, Subgroup.closure_le]
    rintro y ⟨hy, hy7⟩
    have hyC := le_centralizer_of_pow_seven_core hT hN hAL hO2L hTN h207 he hKN hi hy hy7
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun q hq => ?_)
    exact (Subgroup.mem_centralizer_iff.mp (hyC hq) y rfl).symm
  obtain ⟨-, n', F, _, _, hF, hKQ, -, -, -, β₀, hβs₀, hβk₀, -⟩ := hi
  have hQ2 : IsPGroup 2 Q := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le c134Q_le
  have hQ1 : Q ≠ ⊥ := by
    intro hbot
    have hβinj := injective_of_ker_eq β₀ hβk₀
    have hcard : Nat.card (Multiplicative (Fin 3 → F)) = Nat.card Q :=
      Nat.card_congr (MulEquiv.ofBijective β₀ ⟨hβinj, hβs₀⟩).symm.toEquiv
    rw [hbot, Subgroup.card_bot] at hcard
    have h1 : 1 < Nat.card (Multiplicative (Fin 3 → F)) := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun]
      have : 1 < Nat.card F := Finite.one_lt_card
      exact Nat.one_lt_pow (by norm_num) this
    omega
  have hKM : kTwenty M c ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hMK : M ≤ Subgroup.normalizer (kTwenty M c : Set G) := le_normalizer_normalClosureIn M c
  have hTQ : T ≤ Subgroup.normalizer (Q : Set G) := by
    intro t ht
    have h1 : (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)).map (MulAut.conj t).toMonoidHom =
        CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) :=
      map_conj_eq_of_mem_normalizer
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_right ht))
    have h2 : (kTwenty M c).map (MulAut.conj t).toMonoidHom = kTwenty M c :=
      map_conj_eq_of_mem_normalizer (hMK (hT.sylow.le ht))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hQdef, CFSG.Quasithin.c134Q,
      Subgroup.map_commutator]
    exact congrArg₂ (fun A B : Subgroup G => ⁅A, B⁆) h1 h2
  have hKTQ : ((kTwenty M c ⊔ T : Subgroup G) : Set G) ⊆
      (Subgroup.normalizer (Q : Set G) : Set G) := sup_le hKQ hTQ
  obtain ⟨M', hM', hNM'⟩ := exists_mem_scriptM_of_isTwoLocal ⟨Q, hQ1, hQ2, rfl⟩ hKTQ
  rw [h204, Set.mem_singleton_iff] at hM'
  exact hLM (hM' ▸ hLQ.trans hNM')

theorem false_of_caseOne_L32 (h184 : Sec18.Item184_1) {A M L N : Subgroup G} {c : G}
    {T : Subgroup G} (hT : Ctx20One G A M L N c T) (hTN : T ≤ N)
    (h204 : scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G) = {M})
    (h207 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (he : Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃* projSL 3 (GaloisField 2 1)))
    (hKN : ¬ kTwenty M c ≤ N)
    (hi : CFSG.Quasithin.IsC134Case 1 (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c)) :
    False := by
  obtain ⟨H, hH18, -, hL, hN⟩ := exists_sec18H_of_ctx20One hT
  have hLp : ⁅L, L⁆ = L := by
    rw [hL]
    exact Sec18.commutator_eq_of_mem_oTwoComponentsIn
      (mem_scriptH_iff.mp hH18.mem_scriptH).2.2.1
  exact false_of_caseOne_L32_core hT.toCtx20 hN (le_normalizer_of_hyp201One hT.hyp201One)
    (nonempty_quotient_of_hyp201One h184 hT.hyp201One) hLp (not_le_of_hyp201One hT.hyp201One)
    (pCoreOf_le_of_hyp201One hT.hyp201One) hTN h204 h207 he hKN hi

theorem step208CaseOneL32_proof (h184 : Sec18.Item184_1) : Step208CaseOneL32 := by
  intro G _ _ A M L N c T hT hTN h204 h207 he hKN _ _ hi
  exact (false_of_caseOne_L32 h184 hT hTN h204 h207 he hKN hi).elim

end Main

end CFSG.RankThree.PartTwo.Sec20.Res3
