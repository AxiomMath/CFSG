module

public import CFSG.LocalAnalysis.WeakClosure81.FourElevenMonomialL3
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenMonomialU3
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenComplement
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4S3
public import CFSG.GroupTheory.PermFinThree
public import CFSG.GroupTheory.SteinbergCBFTSCN
public import CFSG.CGT.Timmesfeld75.JLemmaTrans
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathPlane
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenVocab

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.E2P.Asc80
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)

variable {Q : Type} [Group Q] [Finite Q]

theorem exists_monomial_frame {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup Q}
    (hL : LieModel ↥L .PSL 3 p 1 ∨ LieModel ↥L .PSU 3 p 1) {W : Subgroup Q} (hWL : W ≤ L)
    (hW : IsElemAbelian 2 W) (hW4 : Nat.card W = 4) :
    ⁅L ⊓ centralizer (W : Set Q), L ⊓ centralizer (W : Set Q)⁆ = ⊥ ∧
      (L ⊓ centralizer (W : Set Q)).relIndex (L ⊓ normalizer (W : Set Q)) = 6 ∧
      ∃ X₀ : Subgroup Q, X₀ ≤ L ⊓ normalizer (W : Set Q) ∧
        X₀ ⊓ (L ⊓ centralizer (W : Set Q)) = pCoreOf 2 (L ⊓ centralizer (W : Set Q)) ∧
        X₀ ⊔ (L ⊓ centralizer (W : Set Q)) = L ⊓ normalizer (W : Set Q) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases hL with hL | hL
  · obtain ⟨e⟩ := exists_equiv_psl3 (p := p)
      (hL.statedClassicalModel_of_ne_zero (by norm_num))
    exact exists_monomial_frame_psl3 (p := p) hp2 e hWL hW hW4
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ :=
      exists_equiv_psu3 (p := p) (hL.statedClassicalModel_of_ne_zero (by norm_num))
    exact exists_monomial_frame_psu3 (p := p) hp2 hF e.symm hWL hW hW4

theorem exists_frame_complement {M N B X₀ S R : Subgroup Q}
    (hMN : M ≤ N) (hBM : B ≤ M) (hBn : N ≤ Subgroup.normalizer (B : Set Q))
    (hMn : N ≤ Subgroup.normalizer (M : Set Q)) (hMB : ⁅M, M⁆ ≤ B)
    (hodd : Odd (B.relIndex M)) (hX₀N : X₀ ≤ N) (hX₀M : X₀ ⊓ M = B)
    (hX₀sup : X₀ ⊔ M = N) (h6 : M.relIndex N = 6) (hSyl : IsSylowIn 2 S N)
    (hR2 : IsPGroup 2 R) (hRN : R ≤ Subgroup.normalizer (N : Set Q))
    (hRM : R ≤ Subgroup.normalizer (M : Set Q))
    (hRB : R ≤ Subgroup.normalizer (B : Set Q))
    (hRS : R ≤ Subgroup.normalizer (S : Set Q)) :
    ∃ X : Subgroup Q, B ≤ X ∧ X ≤ N ∧ X ⊓ M = B ∧ X ⊔ M = N ∧ S ≤ X ∧
      R ≤ Subgroup.normalizer (X : Set Q) := by
  have hX₀nM : X₀ ≤ Subgroup.normalizer (M : Set Q) := hX₀N.trans hMn
  have hBrelX₀ : B.relIndex X₀ = 6 := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := X₀) (K := M) hX₀nM).2
    rw [hX₀sup, hX₀M] at h
    rw [← h, h6]
  have hBX₀ : B ≤ X₀ := by rw [← hX₀M]; exact inf_le_left
  have hrelB : B.relIndex X₀ * X₀.relIndex N = B.relIndex M * M.relIndex N := by
    have h1 : B.relIndex X₀ * X₀.relIndex N = B.relIndex N :=
      Subgroup.relIndex_mul_relIndex B X₀ N hBX₀ hX₀N
    have h2 : B.relIndex M * M.relIndex N = B.relIndex N :=
      Subgroup.relIndex_mul_relIndex B M N hBM hMN
    rw [h1, h2]
  have hX₀rel : X₀.relIndex N = B.relIndex M := by
    have h : 6 * X₀.relIndex N = B.relIndex M * 6 := by
      simpa [hBrelX₀, h6] using hrelB
    have h2 : 6 * X₀.relIndex N = 6 * B.relIndex M := by
      rw [mul_comm (B.relIndex M) 6] at h
      exact h
    exact (Nat.mul_left_cancel_iff (by norm_num : 0 < (6 : ℕ))).mp h2
  have hoddX₀N : Odd (X₀.relIndex N) := by rw [hX₀rel]; exact hodd
  have hnot2X₀N : ¬ 2 ∣ X₀.relIndex N := hoddX₀N.not_two_dvd_nat
  obtain ⟨P, hPsylX₀, -⟩ :=
    exists_isSylowIn_ge (p := 2) (H := X₀) (P := ⊥) bot_le IsPGroup.of_bot
  have hPX₀ : P ≤ X₀ := hPsylX₀.le
  have hPsylN : IsSylowIn 2 P N := by
    refine ⟨hPX₀.trans hX₀N, hPsylX₀.isPGroup, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex P X₀ N hPX₀ hX₀N]
    intro h
    rcases Nat.Prime.dvd_mul Nat.prime_two |>.mp h with h | h
    · exact hPsylX₀.not_dvd_relIndex h
    · exact hnot2X₀N h
  obtain ⟨c, hcN, hcS⟩ :=
    CFSG.Quasithin.B6.isSylowTwoOf_exists_conj (H := N) hPsylN hSyl
  let X₁ : Subgroup Q := CFSG.Quasithin.B6.conjSub c X₀
  have hSX₁ : S ≤ X₁ := by
    rw [hcS]
    exact (CFSG.Quasithin.B6.conjSub c).monotone hPX₀
  have hX₁N : X₁ ≤ N := by
    calc X₁ = CFSG.Quasithin.B6.conjSub c X₀ := rfl
      _ ≤ CFSG.Quasithin.B6.conjSub c N :=
        (CFSG.Quasithin.B6.conjSub c).monotone hX₀N
      _ = N := CFSG.Quasithin.B6.conjSub_eq_self (Subgroup.le_normalizer hcN)
  have hX₁M : X₁ ⊓ M = B := by
    have hcM : c ∈ Subgroup.normalizer (M : Set Q) := hMn hcN
    have hcB : c ∈ Subgroup.normalizer (B : Set Q) := hBn hcN
    calc X₁ ⊓ M = CFSG.Quasithin.B6.conjSub c X₀ ⊓ CFSG.Quasithin.B6.conjSub c M := by
          rw [CFSG.Quasithin.B6.conjSub_eq_self hcM]
      _ = CFSG.Quasithin.B6.conjSub c (X₀ ⊓ M) :=
        ((CFSG.Quasithin.B6.conjSub c).map_inf X₀ M).symm
      _ = CFSG.Quasithin.B6.conjSub c B := by rw [hX₀M]
      _ = B := CFSG.Quasithin.B6.conjSub_eq_self hcB
  have hX₁sup : X₁ ⊔ M = N := by
    have hcM : c ∈ Subgroup.normalizer (M : Set Q) := hMn hcN
    calc X₁ ⊔ M = CFSG.Quasithin.B6.conjSub c X₀ ⊔ CFSG.Quasithin.B6.conjSub c M := by
          rw [CFSG.Quasithin.B6.conjSub_eq_self hcM]
      _ = CFSG.Quasithin.B6.conjSub c (X₀ ⊔ M) :=
        ((CFSG.Quasithin.B6.conjSub c).map_sup X₀ M).symm
      _ = CFSG.Quasithin.B6.conjSub c N := by rw [hX₀sup]
      _ = N := CFSG.Quasithin.B6.conjSub_eq_self (Subgroup.le_normalizer hcN)
  have hBX₁ : B ≤ X₁ := by rw [← hX₁M]; exact inf_le_left
  exact exists_complement_normalized_of_odd (N := N) (M := M) (B := B) (X₀ := X₁)
    (S := S) (R := R) hBM hMN hBn hMn hMB hodd hBX₁ hX₁N hX₁M hX₁sup
    hSX₁ hR2 hRN hRM hRB hRS

theorem bar2_and_pCore_of_complement {L M N B X W : Subgroup Q}
    (hXL : X ≤ L) (hXN : X ≤ N) (hXM : X ⊓ M = B)
    (hXsup : X ⊔ M = N) (hMn : N ≤ Subgroup.normalizer (M : Set Q))
    (hMdef : M = L ⊓ Subgroup.centralizer (W : Set Q)) (hBdef : B = pCoreOf 2 M)
    (h6 : M.relIndex N = 6) (hXnW : X ≤ Subgroup.normalizer (W : Set Q))
    (hW : IsElemAbelian 2 W) (hW4 : Nat.card W = 4) (hBX : B ≤ X)
    (hBn : N ≤ Subgroup.normalizer (B : Set Q)) :
    Nonempty (Bar2 X ≃* Equiv.Perm (Fin 3)) ∧ pCoreOf 2 X ≤ B ∧
      ∃ φ : ↥X →* MulAut ↥W, Function.Surjective φ ∧ φ.ker = B.subgroupOf X ∧
        ∀ (x : ↥X) (w : ↥W),
          ((φ x) w : Q) = (x : Q) * (w : Q) * (x : Q)⁻¹ := by
  have hWcomm : IsMulCommutative ↥W := hW.1
  have hXM' : X ⊓ (L ⊓ Subgroup.centralizer (W : Set Q)) = B := by
    rw [← hMdef]; exact hXM
  let φ : ↥X →* MulAut ↥W :=
    W.normalizerMonoidHom.comp (Subgroup.inclusion hXnW)
  have hφker : φ.ker = (X ⊓ (L ⊓ Subgroup.centralizer (W : Set Q))).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨x.2, hXL x.2, ?_⟩
      change (x : Q) ∈ Subgroup.centralizer (W : Set Q)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h := congrArg (fun a : MulAut ↥W => ((a ⟨w, hw⟩ : ↥W) : Q)) hx
      have h' : (x : Q) * w * (x : Q)⁻¹ = w := by
        simpa [φ, Subgroup.normalizerMonoidHom_apply_apply_coe] using h
      calc w * (x : Q) = ((x : Q) * w * (x : Q)⁻¹) * (x : Q) := by rw [h']
        _ = (x : Q) * w := by group
    · rintro ⟨-, -, hxC⟩
      ext w
      have hval : ((φ x) w : Q) = (x : Q) * (w : Q) * (x : Q)⁻¹ := by
        simp [φ, Subgroup.normalizerMonoidHom_apply_apply_coe]
      rw [hval]
      show (x : Q) * (w : Q) * (x : Q)⁻¹ = (w : Q)
      have hcw : (w : Q) * (x : Q) = (x : Q) * (w : Q) :=
        Subgroup.mem_centralizer_iff.mp hxC w w.2
      rw [← hcw]
      group
  have hφkerB : φ.ker = B.subgroupOf X := by rw [hφker, hXM']
  have hXnM : X ≤ Subgroup.normalizer (M : Set Q) := hXN.trans hMn
  have hBrelX : B.relIndex X = 6 := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := X) (K := M) hXnM).2
    rw [hXsup, hXM] at h
    rw [← h, h6]
  have hB2 : IsPGroup 2 B := by
    rw [hBdef]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hXnB : X ≤ Subgroup.normalizer (B : Set Q) := hXN.trans hBn
  have hBnX : (B.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBX).mpr hXnB
  have : (B.subgroupOf X).Normal := hBnX
  have hcardquot : Nat.card (↥X ⧸ B.subgroupOf X) = 6 := by
    simpa [Subgroup.relIndex, Subgroup.index] using hBrelX
  have hK4 : IsKleinFour ↥W :=
    { card_four := hW4
      exponent_two := by
        have hex : Monoid.ExponentExists ↥W :=
          ⟨2, by norm_num, fun x => by
            apply Subtype.ext
            simpa using hW.2 (x : Q) x.2⟩
        have hdvd : Monoid.exponent ↥W ∣ 2 :=
          Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
            apply Subtype.ext
            simpa using hW.2 (x : Q) x.2
        have hpos : 0 < Monoid.exponent ↥W := hex.exponent_pos
        have hne1 : Monoid.exponent ↥W ≠ 1 := by
          intro h1
          have hsub : Subsingleton ↥W := Monoid.exp_eq_one_iff.mp h1
          have hcard1 : Nat.card ↥W = 1 :=
            Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
          omega
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact absurd h hne1
        · exact h }
  have hcardφ : Nat.card φ.range = 6 := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    rw [show Nat.card (↥X ⧸ φ.ker) = Nat.card (↥X ⧸ B.subgroupOf X) by
      rw [hφkerB]]
    exact hcardquot
  have hcardAut : Nat.card (MulAut ↥W) = 6 := kleinFour_automorphism_card ↥W
  have hrange_top : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcardφ, hcardAut]
  have hφsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp hrange_top
  have hker' : B.subgroupOf X = φ.ker := hφkerB.symm
  let eXB : (↥X ⧸ B.subgroupOf X) ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.quotientMulEquivOfEq hker').trans
      ((QuotientGroup.quotientKerEquivRange φ).trans
        ((MulEquiv.subgroupCongr hrange_top).trans
          (Subgroup.topEquiv.trans (kleinFourAutomorphismEquivSymmetricThree ↥W))))
  have hbar2 : Nonempty (Bar2 X ≃* Equiv.Perm (Fin 3)) := by
    have h := nonempty_oTwoQuot_equiv_perm_of_quotient hBX hB2 hBnX eXB
    simpa [Bar2] using h
  have hpcoreAut : CFSG.pCore 2 (MulAut ↥W) = ⊥ := by
    have hmap := CFSG.pCore_map_iso 2 (kleinFourAutomorphismEquivSymmetricThree ↥W)
    rw [CFSG.GroupTheory.pCore_two_perm_fin_three] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective
      (H := CFSG.pCore 2 (MulAut ↥W))
      (MulEquiv.injective (kleinFourAutomorphismEquivSymmetricThree ↥W))).mp hmap
  have hmap := CFSG.LieType.BorelTits.map_pCore_le (r := 2) φ hφsurj
  rw [hpcoreAut] at hmap
  have hker : CFSG.pCore 2 ↥X ≤ B.subgroupOf X := by
    rw [← hφkerB]
    exact (Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 ↥X) (f := φ)).mp
      (le_bot_iff.mp hmap)
  have hpcoreX_le_B : pCoreOf 2 X ≤ B := by
    calc pCoreOf 2 X = (CFSG.pCore 2 ↥X).map X.subtype := rfl
      _ ≤ (B.subgroupOf X).map X.subtype := Subgroup.map_mono hker
      _ = B ⊓ X := Subgroup.subgroupOf_map_subtype B X
      _ = B := inf_eq_left.mpr hBX
  exact ⟨hbar2, hpcoreX_le_B, φ, hφsurj, hφkerB, fun x w => by
    simp [φ, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩

theorem exists_permThreeMember_of_frame {L : Subgroup Q} [L.Normal] {T A W : Subgroup Q}
    {z : Q} (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hWL : W ≤ L) (hW : IsElemAbelian 2 W)
    (hW4 : Nat.card W = 4) (hzW : z ∈ W) (hz2 : orderOf z = 2)
    (hab : ⁅L ⊓ centralizer (W : Set Q), L ⊓ centralizer (W : Set Q)⁆ = ⊥)
    (h6 : (L ⊓ centralizer (W : Set Q)).relIndex (L ⊓ normalizer (W : Set Q)) = 6)
    {X₀ : Subgroup Q} (hX₀ : X₀ ≤ L ⊓ normalizer (W : Set Q))
    (hX₀M : X₀ ⊓ (L ⊓ centralizer (W : Set Q)) = pCoreOf 2 (L ⊓ centralizer (W : Set Q)))
    (hX₀sup : X₀ ⊔ (L ⊓ centralizer (W : Set Q)) = L ⊓ normalizer (W : Set Q))
    (hSyl : IsSylowIn 2 (T ⊓ (L ⊓ normalizer (W : Set Q))) (L ⊓ normalizer (W : Set Q)))
    (hR : UniquenessCase.PartTwo.tA T A ≤ normalizer (W : Set Q))
    (hAW : ¬ A ⊓ L ≤ centralizer (W : Set Q)) :
    ∃ X : Subgroup Q, PermThreeMember L T A z X := by
  classical
  have _ : A ≤ T := hAT
  have _ : W ≤ L := hWL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup Q := L ⊓ centralizer (W : Set Q) with hM
  set N : Subgroup Q := L ⊓ normalizer (W : Set Q) with hN
  set B : Subgroup Q := pCoreOf 2 M with hB
  have hMN : M ≤ N := inf_le_inf_left L (Subgroup.centralizer_le_normalizer (W : Set Q))
  have hNL : N ≤ L := inf_le_left
  have hBM : B ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hWcomm : IsMulCommutative ↥W := hW.1
  have hWsq : ∀ x : ↥W, x ^ 2 = 1 := fun x => by
    apply Subtype.ext
    simpa using hW.2 (x : Q) x.2
  have hK4 : IsKleinFour ↥W :=
    { card_four := hW4
      exponent_two := by
        have hex : Monoid.ExponentExists ↥W := ⟨2, by norm_num, hWsq⟩
        have hdvd : Monoid.exponent ↥W ∣ 2 :=
          Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hWsq
        have hpos : 0 < Monoid.exponent ↥W := hex.exponent_pos
        have hne1 : Monoid.exponent ↥W ≠ 1 := by
          intro h1
          have hsub : Subsingleton ↥W := Monoid.exp_eq_one_iff.mp h1
          have hcard1 : Nat.card ↥W = 1 :=
            Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
          omega
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact absurd h hne1
        · exact h }
  have hMbot : ⁅M, M⁆ = ⊥ := by simpa [hM] using hab
  have hMB : ⁅M, M⁆ ≤ B := by rw [hMbot]; exact bot_le
  have hoddMB : Odd (B.relIndex M) := by
    have hMcomm : IsMulCommutative ↥M := Subgroup.commutator_self_eq_bot_iff.mp hMbot
    have : IsMulCommutative (↥M ⧸ CFSG.pCore 2 ↥M) :=
      IsMulCommutative.of_comm fun a b => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) a
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) b
        rw [← map_mul, ← map_mul, mul_comm' x y]
    have hcenter : Subgroup.center (↥M ⧸ CFSG.pCore 2 ↥M) = ⊤ := Subgroup.center_eq_top
    have hoddquot : Odd (Nat.card (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      have h := CFSG.CGT.Timmesfeld75.odd_card_center_quot_pCore (R := ↥M)
      simpa [hcenter] using h
    have hsub : (pCoreOf 2 M).subgroupOf M = CFSG.pCore 2 ↥M := by
      rw [pCoreOf, ← Subgroup.comap_subtype, Subgroup.comap_map_eq,
        Subgroup.ker_subtype M, sup_bot_eq]
    rw [hB, Subgroup.relIndex, hsub, Subgroup.index]
    exact hoddquot
  have h6' : M.relIndex N = 6 := by simpa [hM, hN] using h6
  have hLn : N ≤ Subgroup.normalizer (L : Set Q) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have hWn : N ≤ Subgroup.normalizer (W : Set Q) := by rw [hN]; exact inf_le_right
  have hCn : N ≤ Subgroup.normalizer (Subgroup.centralizer (W : Set Q) : Set Q) :=
    CFSG.GroupTheory.FT63ChII.le_normalizer_centralizer hWn
  have hMn : N ≤ Subgroup.normalizer (M : Set Q) := by
    rw [hM]
    exact (le_inf hLn hCn).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hBn : N ≤ Subgroup.normalizer (B : Set Q) := by
    rw [hB]
    exact hMn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) M)
  have hX₀N : X₀ ≤ N := by rw [hN]; exact hX₀
  have hX₀M' : X₀ ⊓ M = B := by simpa [hM, hB] using hX₀M
  have hX₀sup' : X₀ ⊔ M = N := by simpa [hM, hN] using hX₀sup
  set R : Subgroup Q := UniquenessCase.PartTwo.tA T A with hRdef
  have hRT : R ≤ T := CFSG.Quasithin.E1.tauOf_le ⊤ T A
  have hR2 : IsPGroup 2 R := hT.isPGroup.to_le hRT
  have hRL : R ≤ Subgroup.normalizer (L : Set Q) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have hRnW : R ≤ Subgroup.normalizer
      (Subgroup.normalizer (W : Set Q) : Set Q) :=
    fun r hr => CFSG.ABGLocalTools.mem_normalizer_normalizer (hR hr)
  have hRN : R ≤ Subgroup.normalizer (N : Set Q) := by
    rw [hN]
    exact (le_inf hRL hRnW).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hRC : R ≤ Subgroup.normalizer (Subgroup.centralizer (W : Set Q) : Set Q) :=
    CFSG.GroupTheory.FT63ChII.le_normalizer_centralizer hR
  have hRM : R ≤ Subgroup.normalizer (M : Set Q) := by
    rw [hM]
    exact (le_inf hRL hRC).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hRB : R ≤ Subgroup.normalizer (B : Set Q) := by
    rw [hB]
    exact hRM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) M)
  have hRTn : R ≤ Subgroup.normalizer (T : Set Q) := hRT.trans Subgroup.le_normalizer
  have hRS : R ≤ Subgroup.normalizer (T ⊓ N : Subgroup Q) :=
    (le_inf hRTn hRN).trans Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨X, hBX, hXN, hXM, hXsup, hSX, hRX⟩ :=
    exists_frame_complement hMN hBM hBn hMn hMB hoddMB hX₀N hX₀M' hX₀sup' h6'
      hSyl hR2 hRN hRM hRB hRS
  have hXL : X ≤ L := hXN.trans hNL
  have hXnW : X ≤ Subgroup.normalizer (W : Set Q) :=
    hXN.trans (by rw [hN]; exact inf_le_right)
  obtain ⟨hbar2, hpcoreX_le_B, φ₀, hφsurj₀, -, hφapply⟩ :=
    bar2_and_pCore_of_complement hXL hXN hXM hXsup hMn hM hB h6' hXnW hW hW4
      hBX hBn
  let φ : ↥X →* MulAut ↥W := φ₀
  have hφsurj : Function.Surjective φ := hφsurj₀
  have hTXN : T ⊓ X = T ⊓ N := by
    refine le_antisymm (fun x hx => ⟨hx.1, hXN hx.2⟩) (fun x hx => ⟨hx.1, hSX hx⟩)
  have hsylow : IsSylowIn 2 (T ⊓ X) X := by
    have h := CFSG.Quasithin.B6.isSylowTwoOf_mono hSyl hSX hXN
    have h' : IsSylowIn 2 (T ⊓ N) X := ⟨h.1, h.2.1, h.2.2⟩
    simpa [hTXN] using h'
  have htA_le_normalizer : R ≤ Subgroup.normalizer (X : Set Q) := hRX
  have htA_inf_le : R ⊓ L ≤ X := by
    have hRinf : R ⊓ L ≤ T ⊓ N := by
      refine le_inf (inf_le_left.trans hRT) ?_
      rw [hN]
      exact le_inf inf_le_right (inf_le_left.trans hR)
    exact hRinf.trans hSX
  have hnot_inf_le_pCore : ¬ A ⊓ L ≤ pCoreOf 2 X := by
    intro hle
    apply hAW
    exact hle.trans (hpcoreX_le_B.trans (hBM.trans (by rw [hM]; exact inf_le_right)))
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3dvd : 3 ∣ Nat.card (Equiv.Perm (Fin 3)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num
  obtain ⟨p3, hp3⟩ := exists_prime_orderOf_dvd_card' (G := Equiv.Perm (Fin 3)) 3 h3dvd
  let a : MulAut ↥W := (kleinFourAutomorphismEquivSymmetricThree ↥W).symm p3
  have ha : orderOf a = 3 := by
    rw [← (kleinFourAutomorphismEquivSymmetricThree ↥W).orderOf_eq a,
      show (kleinFourAutomorphismEquivSymmetricThree ↥W) a = p3 from by simp [a]]
    exact hp3
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    omega
  have hz1' : (⟨z, hzW⟩ : ↥W) ≠ 1 := by
    intro h
    exact hz1 (congrArg Subtype.val h)
  have hmove : a ⟨z, hzW⟩ ≠ ⟨z, hzW⟩ :=
    (kleinFour_order_three_cycle ↥W a ha ⟨z, hzW⟩ hz1').1
  obtain ⟨c, hcφ⟩ := hφsurj a
  refine ⟨X, hXL, hbar2, hsylow, htA_le_normalizer, htA_inf_le,
    hnot_inf_le_pCore, ?_⟩
  refine ⟨(c : Q), c.2, ?_, ?_⟩
  · intro hconj
    have hzfix : (φ c) ⟨z, hzW⟩ = ⟨z, hzW⟩ := by
      apply Subtype.ext
      rw [hφapply]
      exact hconj
    exact hmove (by rw [hcφ] at hzfix; exact hzfix)
  · have hmem : (c : Q) * z * (c : Q)⁻¹ ∈ W := by
      have h := ((φ c) ⟨z, hzW⟩).2
      rw [hφapply c ⟨z, hzW⟩] at h
      exact h
    have hcommW : (⟨(c : Q) * z * (c : Q)⁻¹, hmem⟩ : ↥W) * ⟨z, hzW⟩ =
        ⟨z, hzW⟩ * ⟨(c : Q) * z * (c : Q)⁻¹, hmem⟩ :=
      mul_comm' _ _
    exact congrArg Subtype.val hcommW

end CFSG.LocalAnalysis.WeakClosure81.FourEleven
