module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1521TDefs
import CFSG.RankThree.PartTwo.Sec15.Gagen1521TMul
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm35Aux2
import CFSG.GH74.GLS.Stage2.Bender.Thm1.L64Setup
import CFSG.HardMathSupport.Solomon.Coordinator.Generation228

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1521T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isCharacteristicP_sup_of_ext1521 {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h146 : Item146 A (lB A)) (h1444 : Item1444 A (lB A))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) {P X T : Subgroup G}
    (hE : Ext1521 A P X T) (hPQ : P ∈ scriptQ A (lB A)) (hPe : CFSG.Assembly.IsElemAbelian p P)
    (hP1 : P ≠ ⊥) (hPA : P = ⁅P, A⁆)
    (hPT : ((P ⊔ T : Subgroup G) : Set G) = (T : Set G) * (P : Set G))
    (hsolv : Group.IsSolvable ↥(P ⊔ T))
    (hprimes : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥(P ⊔ T) → r = 2 ∨ r = p) :
    IsCharacteristicP 2 ↥(P ⊔ T) ∧ T ≠ ⊥ := by
  have hp : p.Prime := Fact.out
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := h.toSec14Std.isE27
  have hA3 : IsPGroup 3 A := hA.isPGroup
  set P₀ : Subgroup G := CFSG.Open.pCoreOf p (P ⊔ T) with hP₀def
  have hAP : A ≤ Subgroup.normalizer ((P ⊔ T : Subgroup G) : Set G) :=
    le_normalizer_sup hPQ.1.2.2 hE.mem_t.1.1.1.2.2
  have hAP₀ : A ≤ Subgroup.normalizer (P₀ : Set G) :=
    hAP.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p (P ⊔ T))
  have hHP₀ : (P ⊔ T : Subgroup G) ≤ Subgroup.normalizer (P₀ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf p (P ⊔ T)
  have hP₀p : IsPGroup p P₀ :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup p (P ⊔ T)
  have hP₀H : P₀ ≤ P ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le p (P ⊔ T)
  have hPp : IsPGroup p P := hPe.isPGroup
  have hT2 : IsPGroup 2 T := isPGroup_of_mem_scriptQPi Nat.prime_two hE.mem_t
  have hP₀P : P₀ ≤ P := by
    intro x hx
    have hxTP : x ∈ (T : Set G) * (P : Set G) := by
      rw [← hPT]
      exact hP₀H hx
    obtain ⟨t, ht, y, hy, rfl⟩ := hxTP
    have htP : t ∈ P₀ ⊔ P := by
      have h1 : t * y ∈ P₀ ⊔ P := (le_sup_left : P₀ ≤ P₀ ⊔ P) hx
      have h2 : y⁻¹ ∈ P₀ ⊔ P := (le_sup_right : P ≤ P₀ ⊔ P) (P.inv_mem hy)
      simpa using (P₀ ⊔ P).mul_mem h1 h2
    have hP₀Pp : IsPGroup p ↥(P₀ ⊔ P) :=
      IsPGroup.to_sup_of_normal_left' (H := P₀) (K := P) hP₀p hPp
        ((le_sup_left : P ≤ P ⊔ T).trans hHP₀)
    have hdisj : Disjoint T (P₀ ⊔ P) :=
      IsPGroup.disjoint_of_ne 2 p (Ne.symm hp2) T (P₀ ⊔ P) hT2 hP₀Pp
    have htbot : t ∈ (⊥ : Subgroup G) := by
      have hmem : t ∈ T ⊓ (P₀ ⊔ P) := ⟨ht, htP⟩
      rwa [hdisj.eq_bot] at hmem
    subst htbot
    simpa using hy
  have hP₀Q : P₀ ∈ scriptQ A (lB A) := mem_scriptQ_of_le hPQ hP₀P hAP₀
  have hnot3P : ¬ 3 ∣ Nat.card P :=
    (isPiSubgroup_piCompl_iff Nat.prime_three P).mp hPQ.1.2.1
  have hcop3P : Nat.Coprime 3 (Nat.card P) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnot3P
  haveI : IsMulCommutative P := hPe.1
  have hfit : ⁅P, A⁆ ⊓ Subgroup.centralizer (A : Set G) = ⊥ :=
    CFSG.SignalizerFunctorTheorem.McBride.Near.Thm35.commutator_inf_centralizer_eq_bot
      (p := 3) Nat.prime_three hA3 hPQ.1.2.2 hcop3P
  have hPCbot : P ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
    rw [hPA]
    exact hfit
  have hP₀Cbot : P₀ ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
    rw [eq_bot_iff]
    exact (inf_le_inf_right _ hP₀P).trans (le_of_eq hPCbot)
  obtain ⟨n, hn⟩ := hP₀p.exists_card_eq
  have hcop3p : Nat.Coprime 3 p :=
    (Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3)
  have hcop3P₀ : Nat.Coprime 3 (Nat.card P₀) := by
    rw [hn]
    exact Nat.Coprime.pow_right n hcop3p
  have hnot3P₀ : ¬ 3 ∣ Nat.card P₀ :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop3P₀
  have hca : P₀ ≤ ⁅P₀, A⁆ ⊔ P₀ ⊓ Subgroup.centralizer (A : Set G) :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.L64.le_commutator_sup_inf_centralizer
      (p := 3) Nat.prime_three hA3 hAP₀ hnot3P₀
  have hP₀comm : P₀ = ⁅P₀, A⁆ := by
    refine le_antisymm ?_
      (CFSG.GH74.GLS.Stage2.Bender.Thm1.L64.commutator_le_left_of_le_normalizer hAP₀)
    refine hca.trans ?_
    rw [hP₀Cbot, sup_bot_eq]
  set V : Subgroup G := CFSG.Open.pCoreOf 2 X with hVdef
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hVX : V ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hXV : X ≤ Subgroup.normalizer (V : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hVpp : V ≤ pPrimeCoreOf 3 X := by
    have h32 : Nat.Coprime 3 2 := by norm_num
    obtain ⟨k, hk⟩ := hV2.exists_card_eq
    refine le_pPrimeCoreOf hVX hXV ?_
    rw [hk]
    exact Nat.Coprime.pow_right k h32
  have hP₀X : P₀ ≤ X := hP₀P.trans hE.le_x
  have hP₀V : P₀ ≤ Subgroup.normalizer (V : Set G) := hP₀X.trans hXV
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hE.mem_y2.1.2
  have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
    hAX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hppInv : pPrimeCoreOf 3 X ∈ invariantPiSubgroups ⊤ A (piCompl 3) := by
    refine ⟨le_top, ?_, ?_⟩
    · exact (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 X))
    · exact hAX.trans (normalizer_le_normalizer_pPrimeCoreOf 3 X)
  have hVinv : V ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, isPiSubgroup_piCompl_of_le hppInv.2.1 hVpp, hAV⟩
  have hΔ : ∀ Z ∈ invariantPiSubgroups ⊤ A (piCompl 3), delta A (lB A) Z ∈ scriptQ A (lB A) :=
    fun Z hZ => delta_mem_scriptQ hA h146 hZ
  set D : Subgroup G := delta A (lB A) V with hDdef
  have hDQ : D ∈ scriptQ A (lB A) := hΔ V hVinv
  have hDV : D ≤ V := delta_le V
  have hD2 : IsPGroup 2 D := hV2.to_le hDV
  have hP₀D : P₀ ≤ Subgroup.normalizer (D : Set G) :=
    (le_delta hP₀Q le_rfl).trans (delta_le_normalizer_delta hΔ hVinv hP₀V)
  have hTX : T ≤ X := hE.mem_t.1.2
  have hTD : T ≤ Subgroup.normalizer (D : Set G) :=
    (le_delta hE.mem_t.1.1 le_rfl).trans (delta_le_normalizer_delta hΔ hVinv (hTX.trans hXV))
  set Z : Subgroup G := ⁅D, P₀⁆ with hZdef
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.L64.le_normalizer_commutator hDQ.1.2.2 hAP₀
  have hZD : Z ≤ D :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.L64.commutator_le_left_of_le_normalizer hP₀D
  have hZQ : Z ∈ scriptQ A (lB A) := mem_scriptQ_of_le hDQ hZD hAZ
  have hZ2 : IsPGroup 2 Z := hD2.to_le hZD
  have hTP₀ : T ≤ Subgroup.normalizer (P₀ : Set G) :=
    (le_sup_right : T ≤ P ⊔ T).trans hHP₀
  have hTZ : T ≤ Subgroup.normalizer (Z : Set G) :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.L64.le_normalizer_commutator hTD hTP₀
  have hTZQ : T ⊔ Z ∈ scriptQ A (lB A) :=
    sup_mem_scriptQ_of_item146 hA h146 hE.mem_t.1.1 hZQ hTZ
  have hTZX : T ⊔ Z ≤ X := sup_le hTX (hZD.trans (hDV.trans hVX))
  have hTZ2 : IsPGroup 2 ↥(T ⊔ Z) :=
    IsPGroup.to_sup_of_normal_right' (H := T) (K := Z) hT2 hZ2 hTZ
  have hTZmem : T ⊔ Z ∈ scriptQPi A (lB A) X (piOf 2) :=
    ⟨⟨hTZQ, hTZX⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hTZ2⟩
  have hcard : Nat.card ↥(T ⊔ Z) ≤ Nat.card T :=
    hE.card_le X hE.mem_y2 hE.le_x (T ⊔ Z) hTZmem
  have hTeq : T ⊔ Z = T := (Subgroup.eq_of_le_of_card_ge le_sup_left hcard).symm
  have hZT : Z ≤ T := hTeq ▸ le_sup_right
  have hZP₀ : Z ≤ Subgroup.normalizer (P₀ : Set G) := hZT.trans hTP₀
  have hP₀Z : P₀ ≤ Subgroup.normalizer (Z : Set G) :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.L64.le_normalizer_commutator hP₀D Subgroup.le_normalizer
  have hcommZbot : ⁅Z, P₀⁆ = ⊥ := by
    have hdisj : Disjoint Z P₀ :=
      IsPGroup.disjoint_of_ne 2 p (Ne.symm hp2) Z P₀ hZ2 hP₀p
    refine eq_bot_iff.mpr ?_
    exact (le_inf
      (CFSG.GH74.GLS.Stage2.Bender.Thm1.L64.commutator_le_left_of_le_normalizer hP₀Z)
      (CFSG.GH74.GLS.Stage2.Bender.Thm1.L64.commutator_le_right_of_le_normalizer hZP₀)).trans
      (le_of_eq hdisj.eq_bot)
  have hnotp2 : ∀ {U : Subgroup G}, IsPGroup 2 U → ¬ p ∣ Nat.card U := by
    intro U hU
    have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
    obtain ⟨k, hk⟩ := hU.exists_card_eq
    rw [hk]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.Coprime.pow_right k hcop2)
  have hZbot : Z = ⊥ := by
    have h : ⁅Z, P₀⁆ = Z := by
      rw [hZdef]
      exact CFSG.HardMathSupport.Solomon.Coordinator.Generation228.comm_comm_eq hp hP₀p hP₀D
        (hnotp2 hD2)
    rw [hcommZbot] at h
    exact h.symm
  have hQE : ∀ E : Subgroup G, IsHyperplane A E →
      ⁅P₀ ⊓ Subgroup.centralizer (E : Set G), A⁆ ≤ Subgroup.centralizer (V : Set G) := by
    intro E hEA
    set Q : Subgroup G := ⁅P₀ ⊓ Subgroup.centralizer (E : Set G), A⁆ with hQdef
    have hQ0 : Q ∈ scriptQZero A (lB A) :=
      commutator_inf_centralizer_mem_scriptQZero hA hP₀Q hEA.1
    have hQle : Q ≤ P₀ ⊓ Subgroup.centralizer (E : Set G) :=
      commutator_inf_centralizer_le hA.1.1 hAP₀ hEA.1
    have hQP₀ : Q ≤ P₀ := hQle.trans inf_le_left
    have hQcE : Q ≤ Subgroup.centralizer (E : Set G) := hQle.trans inf_le_right
    have hQp : IsPGroup p Q := hP₀p.to_le hQP₀
    have hQV : Q ≤ Subgroup.normalizer (V : Set G) := hQP₀.trans hP₀V
    have hE9 : 3 ^ 2 ≤ Nat.card E := by
      have h := hEA.2
      rw [hA.2] at h
      have h9 : (3 : ℕ) ^ 2 = 9 := by norm_num
      rw [h9]
      omega
    have hV3 : Nat.Coprime 3 (Nat.card V) := by
      have h32 : Nat.Coprime 3 2 := by norm_num
      obtain ⟨k, hk⟩ := hV2.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k h32
    rw [Subgroup.le_centralizer_iff]
    refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three
      (Sec5.isElemAbelian_of_le hA.1 hEA.1) hE9 (hEA.1.trans hAV) hV3 fun b hb hb1 => ?_
    have hbA : b ∈ A := hEA.1 hb
    have hQb : Q ≤ Subgroup.centralizer ({b} : Set G) :=
      hQcE.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
    have hAb : A ≤ Subgroup.normalizer
        ((Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G) :=
      le_trans (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨b, hbA⟩))) Subgroup.le_normalizer
    set Vb : Subgroup G := V ⊓ Subgroup.centralizer ({b} : Set G) with hVbdef
    have hQVb : Q ≤ Subgroup.normalizer (Vb : Set G) :=
      Late.le_normalizer_inf hQV (hQb.trans Subgroup.le_normalizer)
    have hle1 : ⁅Q, Vb⁆ ≤ delta A (lB A) (pPrimeCoreOf 3 X) :=
      (Subgroup.commutator_mono le_rfl (inf_le_inf_right _ hVpp)).trans
        (commutator_inf_centralizer_le_delta h1444 hA.1.1 hAX hbA hb1 ⟨hQ0, hQb⟩
          (hQP₀.trans hP₀X))
    have hAQVb : A ≤ Subgroup.normalizer ((⁅Q, Vb⁆ : Subgroup G) : Set G) :=
      CFSG.GH74.GLS.Stage2.Bender.Thm1.L64.le_normalizer_commutator hQ0.1.1.2.2
        (Late.le_normalizer_inf hAV hAb)
    have hQVbQ : ⁅Q, Vb⁆ ∈ scriptQ A (lB A) :=
      mem_scriptQ_of_le (hΔ _ hppInv) hle1 hAQVb
    have hQVbV : ⁅Q, Vb⁆ ≤ V :=
      (Subgroup.commutator_mono le_rfl inf_le_left).trans
        (CFSG.GH74.GLS.Stage2.Bender.Thm1.L64.commutator_le_right_of_le_normalizer hQV)
    have hQVbD : ⁅Vb, Q⁆ ≤ D := by
      rw [Subgroup.commutator_comm]
      exact le_delta hQVbQ hQVbV
    have hVbQ : ⁅Vb, Q⁆ = ⊥ := by
      have hcc := CFSG.HardMathSupport.Solomon.Coordinator.Generation228.comm_comm_eq hp hQp hQVb
        (hnotp2 (hV2.to_le inf_le_left))
      rw [← hcc, eq_bot_iff, ← hZbot]
      exact Subgroup.commutator_mono hQVbD hQP₀
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hVbQ
  have hP₀CenV : P₀ ≤ Subgroup.centralizer (V : Set G) :=
    (le_iSup_commutator_centralizer hA hnot3P₀ hAP₀ hP₀comm).trans (iSup₂_le hQE)
  have hXN : X = Subgroup.normalizer (V : Set G) := by
    refine le_antisymm hXV ?_
    exact hE.normalizer_le
  have hXlocal : CFSG.Open.IsTwoLocal X := ⟨V, hE.mem_y2.2, hV2, hXN⟩
  have hcharX : X ⊓ Subgroup.centralizer (V : Set G) ≤ V := h.charTwoType X hXlocal
  have hP₀V' : P₀ ≤ V := (le_inf hP₀X hP₀CenV).trans hcharX
  have hP₀bot : P₀ = ⊥ := by
    have hdisj : Disjoint P₀ V :=
      IsPGroup.disjoint_of_ne p 2 hp2 P₀ V hP₀p hV2
    have h := hdisj.eq_bot
    rwa [inf_eq_left.mpr hP₀V'] at h
  have h0 : ∀ N : Subgroup G, N ≤ P ⊔ T → (P ⊔ T : Subgroup G) ≤
      Subgroup.normalizer (N : Set G) → IsPGroup p N → N = ⊥ := by
    intro N hNH hnorm hNp
    have hNP₀ : N ≤ P₀ :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p hNH hnorm hNp
    rw [hP₀bot] at hNP₀
    exact le_bot_iff.mp hNP₀
  refine ⟨isCharacteristicP_of_two_p hsolv hprimes h0, ?_⟩
  intro hTbot
  have hH_eq : (P ⊔ T : Subgroup G) = P := by rw [hTbot, sup_bot_eq]
  have hPnorm : (P ⊔ T : Subgroup G) ≤ Subgroup.normalizer (P : Set G) := by
    rw [hH_eq]
    exact Subgroup.le_normalizer
  exact hP1 (h0 P le_sup_left hPnorm hPp)

end CFSG.RankThree.PartTwo.Sec15.Proof1521T
