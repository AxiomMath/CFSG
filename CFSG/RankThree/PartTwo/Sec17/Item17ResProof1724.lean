module

public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProof1724
public import CFSG.RankThree.PartTwo.Sec17.Item1725Proof
import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofX
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec16.Item165ProofTools
import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofDefs
public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProof
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

@[expose] def Item1724LocN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G), Sec17W G A c L Y₀ Y₁ S p P w Q →
      (∀ D ∈ scriptQPi A (lB A) ⊤ (piOf p), D ≠ ⊥ →
        ∀ S' ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (D : Set G)) (piOf p),
        ∀ T' ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (D : Set G)) (piOf p),
          IsConjIn (xA A ⊓ Subgroup.normalizer (D : Set G)) S' T') ∧
      (∀ a ∈ A, a ≠ 1 →
        ∀ S' ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf p),
        ∀ T' ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf p),
          IsConjIn (xA A ⊓ Subgroup.centralizer ({a} : Set G)) S' T')

@[expose] def Item1724LocR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G), Sec17W G A c L Y₀ Y₁ S p P w Q →
      ∀ Y : Subgroup G,
        ((∃ D ∈ scriptQPi A (lB A) ⊤ (piOf p), D ≠ ⊥ ∧ Y = Subgroup.normalizer (D : Set G)) ∨
          ∃ a ∈ A, a ≠ 1 ∧ Y = Subgroup.centralizer ({a} : Set G)) →
        ∃ R : Subgroup G, R ≤ Y ∧ A ≤ Subgroup.normalizer (R : Set G) ∧ ¬ 3 ∣ Nat.card R ∧
          ∀ S' ∈ scriptQPiStar A (lB A) Y (piOf p), S' ≤ R

@[expose] def Claim1724Delta : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G), Sec17W G A c L Y₀ Y₁ S p P w Q →
      Q ⊓ Subgroup.normalizer (Y₀ : Set G) ≠ ⊥ →
        ∃ R ∈ scriptQPiStar A (lB A) ⊤ (piOf p),
          Y₀ = (Y₀ ⊓ Subgroup.centralizer (R : Set G)) ⊔ CFSG.Open.pCoreOf 2 Y₀

namespace Proof17Res

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G} {w : G} {Q : Subgroup G}

theorem false_of_cover_of_le (h : Sec17W G A c L Y₀ Y₁ S p P w Q) {U U' : Subgroup G}
    (hUS : U ≤ S) (hO2U : CFSG.Open.pCoreOf 2 Y₀ ≤ U)
    (hY₀U : Y₀ ≤ Subgroup.normalizer (U : Set G)) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hU'U : U' ≤ U) (hU'O : U' ≤ CFSG.Open.pCoreOf 2 Y₁) (hU'1 : U' ≠ ⊥)
    (hQY : Y₀ = (Y₀ ⊓ Subgroup.centralizer (Q : Set G)) ⊔ CFSG.Open.pCoreOf 2 Y₀) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := h.toSec17Std
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  have hCQP : Y₀ ⊓ Subgroup.centralizer (Q : Set G) ≤ Y₀ ⊓ Subgroup.centralizer (P : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le h.le_Q)
  have hcov : Y₀ ≤ U ⊔ (Y₀ ⊓ Subgroup.centralizer (P : Set G)) := by
    calc Y₀ = (Y₀ ⊓ Subgroup.centralizer (Q : Set G)) ⊔ CFSG.Open.pCoreOf 2 Y₀ := hQY
      _ ≤ U ⊔ (Y₀ ⊓ Subgroup.centralizer (P : Set G)) := sup_le (hCQP.trans le_sup_right)
          (hO2U.trans le_sup_left)
  set X := U ⊔ P with hX
  have hUX : U ≤ Subgroup.normalizer (X : Set G) := le_sup_left.trans Subgroup.le_normalizer
  have hCX : Y₀ ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    intro y hy
    exact mem_normalizer_sup (hY₀U hy.1) (Subgroup.centralizer_le_normalizer _ hy.2)
  have hY₀X : Y₀ ≤ Subgroup.normalizer (X : Set G) := hcov.trans (sup_le hUX hCX)
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec14.le_normalizer_sup hAU h.mem_qStar_p.prop.1.1.1.2.2
  have hXY : X ≤ Y₁ := sup_le (hUS.trans h.mem_qStar_two.prop.1.2) h.mem_qStar_p.prop.1.2
  have hU'X : U' ≤ CFSG.Open.pCoreOf 2 X := by
    refine (le_inf (hU'U.trans le_sup_left) hU'O).trans
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₁).to_le inf_le_right))
    exact Late.le_normalizer_inf Subgroup.le_normalizer
      (hXY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₁))
  have hO2X : CFSG.Open.pCoreOf 2 X ≠ ⊥ := fun hb => hU'1 (le_bot_iff.mp (hb ▸ hU'X))
  have hloc : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer
      ((CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G)) :=
    ⟨_, hO2X, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X, rfl⟩
  have hsub : ((Y₀ ⊔ A : Subgroup G) : Set G) ⊆
      Subgroup.normalizer ((CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G) :=
    SetLike.coe_subset_coe.mpr (sup_le
      (hY₀X.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
      (hAX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)))
  obtain ⟨M', hM', hle⟩ := exists_mem_scriptM_of_isTwoLocal hloc hsub
  change M' ∈ CFSG.maximalTwoLocalsContaining _ at hM'
  rw [hs.scriptM_eq] at hM'
  have hM'eq : M' = M := Set.mem_singleton_iff.mp hM'
  have hPM : P ≤ M := by
    rw [← hM'eq]
    exact (le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)).trans hle
  apply h.commutator_not_le_M
  have hcM : c ∈ M := hs.normalizer_le (Subgroup.le_normalizer hs.c_mem)
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem (hPM hx) (zpow_mem hcM k)) (inv_mem (hPM hx)))
    (inv_mem (zpow_mem hcM k))

theorem le_normalizer_sup_of_le_pCoreOf {Y₀ U' : Subgroup G}
    (hU' : U' ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G))) :
    Y₀ ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y₀ ⊔ U' : Subgroup G) : Set G) := by
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  set O := CFSG.Open.pCoreOf 2 M with hO
  set V := CFSG.Open.pCoreOf 2 Y₀ with hV
  have hMO : M ≤ Subgroup.normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hOM : O ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hYM : Y₀ ≤ M := Subgroup.le_normalizer
  have hYO : Y₀ ⊓ O ≤ V :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (Late.le_normalizer_inf Subgroup.le_normalizer (hYM.trans hMO))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_right)
  have hVY : Y₀ ≤ Subgroup.normalizer (V : Set G) :=
    hYM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀)
  intro y hy
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hle : (V ⊔ U').map (MulAut.conj y).toMonoidHom ≤ V ⊔ U' := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [Late.map_conj_eq_of_mem_normalizer (hVY hy)]
      exact le_sup_left
    · rintro _ ⟨u, hu, rfl⟩
      have hyu : y * u * y⁻¹ * u⁻¹ ∈ V := by
        have hY : y * u * y⁻¹ * u⁻¹ ∈ Y₀ := by
          have h1 : u * y⁻¹ * u⁻¹ ∈ Y₀ :=
            (Subgroup.mem_normalizer_iff.mp (hOM (hU' hu)) y⁻¹).mp (inv_mem hy)
          have : y * u * y⁻¹ * u⁻¹ = y * (u * y⁻¹ * u⁻¹) := by group
          rw [this]
          exact mul_mem hy h1
        have hO' : y * u * y⁻¹ * u⁻¹ ∈ O := by
          have h1 : y * u * y⁻¹ ∈ O :=
            (Subgroup.mem_normalizer_iff.mp (hMO (hYM hy)) u).mp (hU' hu)
          exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hU' hu))
        exact hYO (Subgroup.mem_inf.mpr ⟨hY, hO'⟩)
      have : (MulAut.conj y).toMonoidHom u = (y * u * y⁻¹ * u⁻¹) * u := by
        simp [MulAut.conj_apply]
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left hyu) (Subgroup.mem_sup_right hu)
  exact hle ⟨x, hx, rfl⟩

theorem false_of_cover_O2 (h : Sec17W G A c L Y₀ Y₁ S p P w Q) (h146 : Item146 A (lB A))
    (h166 : Item166 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h179 : Item179 A (lB A)) (hO2 : CFSG.Open.pCoreOf 2 Y₀ ≤ S)
    (hQY : Y₀ = (Y₀ ⊓ Subgroup.centralizer (Q : Set G)) ⊔ CFSG.Open.pCoreOf 2 Y₀) : False := by
  have hs := h.toSec17Std
  have hA : IsE27 A := hs.isE27
  obtain ⟨⟨U', hU', hU'M⟩, hU'Y⟩ := h179 Y₀ hs.mem_y0Star
  have hY₁3 : Y₁ ∈ scriptY3Star A (lB A) :=
    hs.mem_scriptY3Star_of_not_le h166 hbot h.mem_y1Star h.not_le_M
  have hU'O : U' ≤ CFSG.Open.pCoreOf 2 Y₁ := hU'Y U' hU' hU'M Y₁ hY₁3
  have hY₁Q : Y₁ ∈ scriptQ A (lB A) :=
    Proof165.mem_scriptQ_of_three hA h146 h.mem_y1Star.prop.1.2
      h.mem_y1Star.prop.1.1.1.2 (not_three_dvd_of_oPrimeResidualOf_eq_bot' h.mem_y1Star.prop.2)
  have hO2Y₁ : CFSG.Open.pCoreOf 2 Y₁ ≤ S :=
    Proof1721.pCoreOf_le_of_mem_scriptQPiStar hY₁Q h.mem_qStar_two
  have hAV : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₀ : Set G) :=
    hs.le_normalizer_y0.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀)
  have hU'1 : U' ≠ ⊥ := by
    intro hbot'
    have h4 := hU'.1.2.2
    rw [hbot', Subgroup.card_bot] at h4
    omega
  exact false_of_cover_of_le h (U := CFSG.Open.pCoreOf 2 Y₀ ⊔ U') (U' := U')
    (sup_le hO2 (hU'O.trans hO2Y₁)) le_sup_left (le_normalizer_sup_of_le_pCoreOf hU'M.2)
    (Sec14.le_normalizer_sup hAV hU'M.1.1.2.2) le_sup_right hU'O hU'1 hQY

theorem eq_sup_of_isConjIn (h : Sec17W G A c L Y₀ Y₁ S p P w Q) {R : Subgroup G}
    (hRY : Y₀ = (Y₀ ⊓ Subgroup.centralizer (R : Set G)) ⊔ CFSG.Open.pCoreOf 2 Y₀)
    (hRQ : IsConjIn (xA A) R Q) :
    Y₀ = (Y₀ ⊓ Subgroup.centralizer (Q : Set G)) ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
  obtain ⟨x, hx, rfl⟩ := hRQ
  have hxM : x ∈ Subgroup.normalizer (Y₀ : Set G) :=
    HeadProof.centralizer_le_M h.toSec17Std (pPrimeCoreOf_le 3 _ hx)
  have hY : Y₀.map (MulAut.conj x).toMonoidHom = Y₀ := Late.map_conj_eq_of_mem_normalizer hxM
  have hV : (CFSG.Open.pCoreOf 2 Y₀).map (MulAut.conj x).toMonoidHom = CFSG.Open.pCoreOf 2 Y₀ :=
    Late.map_conj_eq_of_mem_normalizer
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀ hxM)
  calc Y₀ = Y₀.map (MulAut.conj x).toMonoidHom := hY.symm
    _ = ((Y₀ ⊓ Subgroup.centralizer (R : Set G)) ⊔ CFSG.Open.pCoreOf 2 Y₀).map
          (MulAut.conj x).toMonoidHom := by rw [← hRY]
    _ = (Y₀ ⊓ Subgroup.centralizer ((R.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G)) ⊔
          CFSG.Open.pCoreOf 2 Y₀ := by
        rw [Subgroup.map_sup, Subgroup.map_inf_eq _ _ _ (MulAut.conj x).injective, hY, hV,
          Sec14.map_conj_centralizer]

theorem isConjIn_of_locN (h : Sec17W G A c L Y₀ Y₁ S p P w Q)
    (hN : ∀ D ∈ scriptQPi A (lB A) ⊤ (piOf p), D ≠ ⊥ →
      ∀ S' ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (D : Set G)) (piOf p),
      ∀ T' ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (D : Set G)) (piOf p),
        IsConjIn (xA A ⊓ Subgroup.normalizer (D : Set G)) S' T')
    (hC : ∀ a ∈ A, a ≠ 1 →
      ∀ S' ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf p),
      ∀ T' ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf p),
        IsConjIn (xA A ⊓ Subgroup.centralizer ({a} : Set G)) S' T')
    {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ∈ scriptQPiStar A (lB A) ⊤ (piOf p))
    (hQ₂ : Q₂ ∈ scriptQPiStar A (lB A) ⊤ (piOf p)) : IsConjIn (xA A) Q₁ Q₂ := by
  have hp : p.Prime := h.p_prime
  have : Fact p.Prime := ⟨hp⟩
  have hA : IsE27 A := h.toSec14Std.isE27
  have hnat := isNaturalFamily_lB A
  have hVA : xA A ≤ Subgroup.normalizer (A : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)
  refine isConjIn_of_maximal (p := p) (A := A)
    (hp := fun Q hQ => isPGroup_of_mem_scriptQPi hp hQ)
    (hA := fun Q hQ => hQ.1.1.1.2.2) (hsub := fun Q hQ R hRQ hAR => mem_scriptQPi_of_le hQ hRQ hAR)
    (hW := fun Q hQ w hw => map_conj_mem_scriptQPi_top hnat (hVA hw) hQ) ?_ hA.1.1 ?_ ?_ hQ₁ hQ₂
  · intro D hD hD0 S' hS' T' hT'
    rw [maxIn_scriptQPi_top] at hS' hT'
    exact hN D hD hD0 S' hS' T' hT'
  · intro a ha ha1 S' hS' T' hT'
    rw [maxIn_scriptQPi_top] at hS' hT'
    exact hC a ha ha1 S' hS' T' hT'
  · intro S' T' hS' hT' hST' _
    exact exists_meet_of_not_isConjIn hp h.three_lt_p.ne' hA hS' hT' hST'

theorem isConjIn_of_le_threePrime (hA : IsE27 A) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (hp : p.Prime) {Y R : Subgroup G} (hRY : R ≤ Y)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hR3 : ¬ 3 ∣ Nat.card R)
    (hle : ∀ S' ∈ scriptQPiStar A (lB A) Y (piOf p), S' ≤ R)
    {S' T' : Subgroup G} (hS : S' ∈ scriptQPiStar A (lB A) Y (piOf p))
    (hT : T' ∈ scriptQPiStar A (lB A) Y (piOf p)) :
    IsConjIn (xA A ⊓ Y) S' T' := by
  have : Fact p.Prime := ⟨hp⟩
  have hA3 : IsPGroup 3 A := hA.isPGroup
  have hRinv : R ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR⟩
  set E := delta A (lB A) R with hE
  have hEQ : E ∈ scriptQ A (lB A) := delta_mem_scriptQ hA h146 hRinv
  have hER : E ≤ R := delta_le R
  have hE3 : ¬ 3 ∣ Nat.card E := fun h => hR3 (h.trans (Subgroup.card_dvd_of_le hER))
  have hAE : A ≤ Subgroup.normalizer (E : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  have hsyl : ∀ S ∈ scriptQPiStar A (lB A) Y (piOf p), CFSG.Open.fusionIsSylowIn p S E ∧
      A ≤ Subgroup.normalizer (S : Set G) := by
    intro S hS
    have hSp : IsPGroup p S := isPGroup_of_mem_scriptQPi hp hS.prop
    have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
    have hSQ : S ∈ scriptQ A (lB A) := hS.prop.1.1
    have hSE : S ≤ E := le_delta hSQ (hle S hS)
    obtain ⟨S'', hS'', hSS'', hAS''⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      Nat.prime_three hp hA3 hE3 hAE hSE hSp hAS
    have hS''mem : S'' ∈ scriptQPi A (lB A) Y (piOf p) :=
      ⟨⟨mem_scriptQ_of_le hEQ hS''.1 hAS'', hS''.1.trans (hER.trans hRY)⟩,
        (isPiSubgroup_piOf_iff hp S'').mpr hS''.2.1⟩
    have := hS.eq_of_le hS''mem hSS''
    exact ⟨this ▸ hS'', hAS⟩
  obtain ⟨hSs, hAS⟩ := hsyl S' hS
  obtain ⟨hTs, hAT⟩ := hsyl T' hT
  obtain ⟨x, hx, hxT⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows Nat.prime_three hp
    hA3 hE3 hAE hSs hTs hAS hAT
  have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1.1
  have hCEA : E ⊓ Subgroup.centralizer (A : Set G) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
    refine le_pPrimeCoreOf_centralizer hbot (mem_scriptQ_of_le hEQ inf_le_left ?_) inf_le_right
    exact le_normalizer_inf hAE (hAC.trans Subgroup.le_normalizer)
  exact ⟨x, ⟨hCEA hx, hER.trans hRY (Subgroup.mem_inf.mp hx).1⟩, hxT⟩

end Proof17Res

open Proof17Res

theorem item1724LocN_of_R (hR : Item1724LocR) (h146 : Item146S14) (hbot : Item145BotS14) :
    Item1724LocN := by
  intro G _ _ A c L Y₀ Y₁ S p P w Q h
  have hp : p.Prime := h.p_prime
  have hA : IsE27 A := h.toSec14Std.isE27
  have h146' := h146 G A c L h.toSec14Std
  have hbot' := hbot G A c L h.toSec14Std
  refine ⟨fun D hD hD0 S' hS' T' hT' => ?_, fun a ha ha1 S' hS' T' hT' => ?_⟩
  · obtain ⟨R, hRY, hAR, hR3, hle⟩ :=
      hR G A c L Y₀ Y₁ S p P w Q h _ (Or.inl ⟨D, hD, hD0, rfl⟩)
    exact isConjIn_of_le_threePrime hA h146' hbot' hp hRY hAR hR3 hle hS' hT'
  · obtain ⟨R, hRY, hAR, hR3, hle⟩ :=
      hR G A c L Y₀ Y₁ S p P w Q h _ (Or.inr ⟨a, ha, ha1, rfl⟩)
    exact isConjIn_of_le_threePrime hA h146' hbot' hp hRY hAR hR3 hle hS' hT'

theorem item1724_two_of_locN (hloc : Item1724LocN) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G} {w : G}
    {Q : Subgroup G} (h : Sec17W G A c L Y₀ Y₁ S p P w Q) :
    ∀ Q₁ ∈ scriptQPiStar A (lB A) ⊤ (piOf p), ∀ Q₂ ∈ scriptQPiStar A (lB A) ⊤ (piOf p),
      IsConjIn (xA A) Q₁ Q₂ := fun _ hQ₁ _ hQ₂ =>
  isConjIn_of_locN h (hloc G A c L Y₀ Y₁ S p P w Q h).1 (hloc G A c L Y₀ Y₁ S p P w Q h).2 hQ₁ hQ₂

theorem claim1724Cover_of (hΔ : Claim1724Delta) (hloc : Item1724LocN) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
      (P : Subgroup G) (w : G) (Q : Subgroup G), Sec17W G A c L Y₀ Y₁ S p P w Q →
        Q ⊓ Subgroup.normalizer (Y₀ : Set G) ≠ ⊥ →
          Y₀ = (Y₀ ⊓ Subgroup.centralizer (Q : Set G)) ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
  intro G _ _ A c L Y₀ Y₁ S p P w Q h hQM
  obtain ⟨R, hR, hRY⟩ := hΔ G A c L Y₀ Y₁ S p P w Q h hQM
  exact eq_sup_of_isConjIn h hRY (item1724_two_of_locN hloc h R hR Q h.mem_qStar_G)

theorem item1724Three_of_O2 (hO2 : Claim17O2Y0) (h146 : Item146S14) (h166 : Item166S17)
    (hbot : Item145BotS17) (h179 : Item179S17) (hΔ : Claim1724Delta) (hloc : Item1724LocN) :
    Item1724Three := by
  intro G _ _ A c L Y₀ Y₁ S p P w Q h
  by_contra hQM
  exact false_of_cover_O2 h (h146 G A c L h.toSec14Std) (h166 G A c L Y₀ h.toSec17Std)
    (hbot G A c L Y₀ h.toSec17Std) (h179 G A c L Y₀ h.toSec17Std)
    (hO2 G A c L Y₀ Y₁ S p P h.toSec17Y1)
    (claim1724Cover_of hΔ hloc G A c L Y₀ Y₁ S p P w Q h hQM)

theorem item1724N_of_res (hloc : Item1724LocN) (hΔ : Claim1724Delta) (hO2 : Claim17O2Y0)
    (h146 : Item146S14) (h166 : Item166S17) (hbot : Item145BotS17) (h179 : Item179S17) :
    Item1724N := fun G _ _ A c L Y₀ Y₁ S p P w Q h =>
  ⟨item1724_two_of_locN hloc h,
    item1724Three_of_O2 hO2 h146 h166 hbot h179 hΔ hloc G A c L Y₀ Y₁ S p P w Q h⟩

end CFSG.RankThree.PartTwo.Sec17
