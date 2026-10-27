module

public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
public import CFSG.RankThree.PartTwo.Sec15.HypS
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec14.Item146General
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof169

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS

open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_ne_bot_of_nine_le {A B E : Subgroup G} (hBA : B ≤ A) (hEA : E ≤ A)
    (hA : Nat.card A = 27) (hB : 9 ≤ Nat.card B) (hE : 9 ≤ Nat.card E) : B ⊓ E ≠ ⊥ := by
  intro hbot
  have h1 := Subgroup.relIndex_inf_le (H := B) (K := E) (L := A)
  rw [hbot, Subgroup.relIndex_bot_left, hA] at h1
  have hB' := Subgroup.relIndex_mul_card B A
  have hE' := Subgroup.relIndex_mul_card E A
  rw [inf_of_le_left hBA, hA] at hB'
  rw [inf_of_le_left hEA, hA] at hE'
  have hBi : B.relIndex A ≤ 3 := by nlinarith
  have hEi : E.relIndex A ≤ 3 := by nlinarith
  nlinarith

theorem nine_le_card_of_lt {A B C : Subgroup G} (hBA : B ≤ A) (hA : Nat.card A = 27)
    (hC : Nat.card C = 3) (hCB : C < B) : 9 ≤ Nat.card B := by
  have hlt : Nat.card C < Nat.card B := Subgroup.card_lt_of_lt hCB
  have hdvd : Nat.card B ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA]
    exact Subgroup.card_dvd_of_le hBA
  obtain ⟨k, hk, hkB⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  rw [hkB, hC] at hlt
  rw [hkB]
  have hk2 : 2 ≤ k := by
    by_contra hk2
    push Not at hk2
    interval_cases k <;> norm_num at hlt
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk2

omit [Finite G] in
theorem card_sup_zpowers_le {x y : G} (hxy : x * y = y * x)
    (hx : Nat.card (Subgroup.zpowers x) = 3) (hy : Nat.card (Subgroup.zpowers y) = 3) :
    Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ≤ 9 := by
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
    refine (Subgroup.zpowers_le.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hxy
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle
  calc Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G)
      = Nat.card (((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G)) := rfl
    _ = Nat.card ((Subgroup.zpowers x : Set G) * (Subgroup.zpowers y : Set G)) := by rw [hcoe]
    _ ≤ Nat.card (Subgroup.zpowers x : Set G) * Nat.card (Subgroup.zpowers y : Set G) :=
        Set.natCard_mul_le
    _ = 9 := by
        change Nat.card (Subgroup.zpowers x) * Nat.card (Subgroup.zpowers y) = 9
        rw [hx, hy]

theorem le_zpowers_sup_of_not_mem {A B : Subgroup G} (hB : IsHyperplane A B) {a : G}
    (ha : a ∈ A) (haB : a ∉ B) : A ≤ Subgroup.zpowers a ⊔ B := by
  set M := Subgroup.zpowers a ⊔ B with hM
  have hBM : B ≤ M := le_sup_right
  have hMA : M ≤ A := sup_le (Subgroup.zpowers_le.mpr ha) hB.1
  have hidx : B.relIndex A = 3 := by
    have h := Subgroup.relIndex_mul_card B A
    rw [inf_of_le_left hB.1, hB.2] at h
    have hpos : 0 < Nat.card B := Nat.card_pos
    nlinarith
  have hprod := Subgroup.relIndex_mul_relIndex B M A hBM hMA
  rw [hidx] at hprod
  have hBM1 : B.relIndex M ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hMB
    exact haB (hMB (le_sup_left (a := Subgroup.zpowers a) (Subgroup.mem_zpowers a)))
  have hdvd : B.relIndex M ∣ 3 := ⟨M.relIndex A, hprod.symm⟩
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h1 | h3
  · exact absurd h1 hBM1
  · rw [h3] at hprod
    have : M.relIndex A = 1 := by omega
    exact Subgroup.relIndex_eq_one.mp this

omit [Finite G] in
theorem le_normalizer_inf {K H₁ H₂ : Subgroup G} (h₁ : K ≤ Subgroup.normalizer (H₁ : Set G))
    (h₂ : K ≤ Subgroup.normalizer (H₂ : Set G)) :
    K ≤ Subgroup.normalizer ((H₁ ⊓ H₂ : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  rw [Subgroup.mem_normalizer_iff.mp (h₁ hx) y, Subgroup.mem_normalizer_iff.mp (h₂ hx) y]

omit [Finite G] in
theorem inf_centralizer_le_of_mem_sup {x y d : G}
    (hd : d ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) :
    Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ≤
      Subgroup.centralizer ({d} : Set G) := by
  rintro g ⟨hgx, hgy⟩
  have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({g} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hgx).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hgy).symm
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp (hle hd)).symm

omit [Finite G] in
theorem centralizer_le_of_zpowers_eq {b c : G} (h : Subgroup.zpowers b = Subgroup.zpowers c) :
    Subgroup.centralizer ({b} : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
  rw [← h, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

omit [Finite G] in
theorem commutator_sup_le {O X A : Subgroup G} (hAO : A ≤ Subgroup.normalizer (O : Set G))
    (hXO : X ≤ Subgroup.normalizer (O : Set G)) (hXA : X ≤ Subgroup.centralizer (A : Set G)) :
    ⁅O ⊔ X, A⁆ ≤ O := by
  rw [Subgroup.commutator_le]
  intro g hg a ha
  have hg' : g ∈ ((O : Set G) * (X : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left O X hXO]
    exact hg
  obtain ⟨o, ho, x, hx, rfl⟩ := hg'
  have hxa : a * x = x * a := Subgroup.mem_centralizer_iff.mp (hXA hx) a ha
  have hxa' : x * a * x⁻¹ = a := by rw [← hxa, mul_inv_cancel_right]
  have heq : ⁅o * x, a⁆ = o * (a * o⁻¹ * a⁻¹) := by
    rw [commutatorElement_def, mul_inv_rev]
    calc o * x * a * (x⁻¹ * o⁻¹) * a⁻¹ = o * (x * a * x⁻¹) * o⁻¹ * a⁻¹ := by group
      _ = o * (a * o⁻¹ * a⁻¹) := by rw [hxa']; group
  rw [heq]
  exact O.mul_mem ho ((Subgroup.mem_normalizer_iff.mp (hAO ha) o⁻¹).mp (O.inv_mem ho))

theorem coprime_three_of_isPGroup_two {Q : Subgroup G} (hQ : IsPGroup 2 Q) :
    Nat.Coprime 3 (Nat.card Q) := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  rw [hk]
  exact Nat.Coprime.pow_right k (by norm_num)

theorem pCoreOf_two_mem_scriptQ {A : Subgroup G} (hAab : IsMulCommutative A) {a : G}
    (ha : a ∈ A) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({a} : Set G)) ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  set Q := CFSG.Open.pCoreOf 2 Ca with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Ca
  have hQCa : Q ≤ Ca := CFSG.LieType.BorelTits.pCoreOf_le 2 Ca
  have hACa : A ≤ Ca := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (by simpa using congrArg Subtype.val (hAab.is_comm.comm ⟨x, hx⟩ ⟨a, ha⟩))
  have hCaQ : Ca ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Ca
  have hQ3 : ¬ 3 ∣ Nat.card Q :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_three_of_isPGroup_two hQ2)
  refine ⟨⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three Q).mpr hQ3, hACa.trans hCaQ⟩,
    fun B hB => ?_⟩
  have hcop : Nat.Coprime 3 (Nat.card (Q ⊓ Subgroup.centralizer (B : Set G) : Subgroup G)) :=
    coprime_three_of_isPGroup_two (hQ2.to_le inf_le_left)
  unfold qBound
  by_cases haB : a ∈ B
  · have hCB : Subgroup.centralizer (B : Set G) ≤ Ca :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB)
    have hle : Q ⊓ Subgroup.centralizer (B : Set G) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) :=
      le_pPrimeCoreOf inf_le_right (le_normalizer_inf (hCB.trans hCaQ) Subgroup.le_normalizer)
        hcop
    exact hle.trans (le_sup_left.trans le_sup_left)
  · have hAM := le_zpowers_sup_of_not_mem hB ha haB
    have hCAB : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (B : Set G) :=
      Subgroup.centralizer_le hB.1
    have hCACa : Subgroup.centralizer (A : Set G) ≤ Ca :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)
    have hleA : Q ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (A : Set G) := by
      rintro x ⟨hxQ, hxB⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hsub : Subgroup.zpowers a ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := by
        refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp (hQCa hxQ)).symm
        · intro z hz
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hxB z hz)
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hsub (hAM hy)))
    have hle : Q ⊓ Subgroup.centralizer (B : Set G) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) :=
      le_pPrimeCoreOf hleA (le_normalizer_inf (hCACa.trans hCaQ)
        (hCAB.trans Subgroup.le_normalizer)) hcop
    exact hle.trans (le_sup_right.trans le_sup_left)

theorem delta_normalizer_mem_scriptY3 (hsimp : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {A C : Subgroup G} (hC1 : C ≠ ⊥) (hC2 : IsPGroup 2 C)
    (hCQ : C ∈ scriptQ A (lB A)) :
    delta A (lB A) (Subgroup.normalizer (C : Set G)) ∈ scriptY3 A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Subgroup.normalizer (C : Set G) with hK
  have hKtop : K ≠ ⊤ := normalizer_ne_top_of_isPGroup hsimp hnab hC1 hC2
  have hCD : C ≤ delta A (lB A) K := le_delta hCQ Subgroup.le_normalizer
  have hCO : C ≤ CFSG.Open.pCoreOf 2 (delta A (lB A) K) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCD (delta_le K) hC2
  refine ⟨⟨⟨fun h => hKtop (top_le_iff.mp (h ▸ delta_le K)), le_normalizer_delta K⟩, ?_⟩,
    (delta_delta K).symm⟩
  intro h0
  rw [h0] at hCO
  exact hC1 (le_bot_iff.mp hCO)

theorem centralizer_le_normalizer_thetaCen (X : Set G) :
    Subgroup.centralizer X ≤ Subgroup.normalizer ((thetaCen X : Subgroup G) : Set G) := by
  have : (aschbacherSolvableCore 3 ↥(Subgroup.centralizer X)).Characteristic :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.1
  exact Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)

theorem le_inSubgroup_theta_of_subnormal {X O T : Subgroup G} (hOX : O ≤ X) (hTO : T ≤ O)
    (hXO : X ≤ Subgroup.normalizer (O : Set G)) (hOT : O ≤ Subgroup.normalizer (T : Set G))
    (hs : Group.IsSolvable ↥T) (h3 : ¬ 3 ∣ Nat.card T) :
    T ≤ inSubgroup (aschbacherSolvableCore 3) X := by
  set T' := T.subgroupOf X with hT'
  set O' := O.subgroupOf X with hO'
  have hO'n : O'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOX).mpr hXO
  have hT'O' : T' ≤ O' := fun x hx => Subgroup.mem_subgroupOf.mpr
    (hTO (Subgroup.mem_subgroupOf.mp hx))
  have hT'n : (T'.subgroupOf O').Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hT'O').mpr fun x hx => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxO : (x : G) ∈ O := Subgroup.mem_subgroupOf.mp hx
    simpa [hT', Subgroup.mem_subgroupOf] using Subgroup.mem_normalizer_iff.mp (hOT hxO) y
  have hsub : T'.IsSubnormal :=
    Subgroup.IsSubnormal.step T' O' hT'O' hO'n.isSubnormal hT'n
  have hTX : T ≤ X := hTO.trans hOX
  have hequiv : ↥T' ≃* ↥T := Subgroup.subgroupOfEquivOfLe hTX
  have hT's : Group.IsSolvable ↥T' :=
    Group.isSolvable_of_isSolvable_injective (f := hequiv.toMonoidHom) hequiv.injective
  have hT'3 : ¬ 3 ∣ Nat.card T' := by
    rwa [Nat.card_congr hequiv.toEquiv]
  have h := solvable_prime_complement_core_subnormal_intersection Nat.prime_three hsub
  have htop : aschbacherSolvableCore 3 ↥T' = ⊤ := by
    refine eq_top_iff.mpr ((solvable_prime_complement_core_characterization
      Nat.prime_three).2.2.2.1 ⊤ inferInstance ?_ ?_)
    · exact Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
    · rwa [Subgroup.card_top]
  have hT'eq : inSubgroup (aschbacherSolvableCore 3) T' = T' := by
    rw [inSubgroup, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hT'eq] at h
  have key : T' ≤ aschbacherSolvableCore 3 ↥X := by
    rw [h]
    exact inf_le_right
  calc T = T'.map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hTX).symm
    _ ≤ inSubgroup (aschbacherSolvableCore 3) X := Subgroup.map_mono key

end CFSG.RankThree.PartTwo.Sec16.Proof169

namespace CFSG.RankThree.PartTwo.Sec16.Proof169

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_of_le {p : ℕ} {A B : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian p A)
    (hBA : B ≤ A) : CFSG.Assembly.IsElemAbelian p B := CFSG.Open.IsElemAbelian.mono hA hBA

theorem zpowers_eq_of_mem_of_ne_one {x c : G} (hc : Nat.card (Subgroup.zpowers c) = 3)
    (hx : x ∈ Subgroup.zpowers c) (hx1 : x ≠ 1) : Subgroup.zpowers x = Subgroup.zpowers c := by
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr hx
  have hdvd : Nat.card (Subgroup.zpowers x) ∣ 3 := hc ▸ Subgroup.card_dvd_of_le hle
  have hne : Nat.card (Subgroup.zpowers x) ≠ 1 := by
    rw [Ne, Subgroup.card_eq_one]
    intro hbot
    exact hx1 (by simpa [hbot] using Subgroup.mem_zpowers x)
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h1 | h3
  · exact absurd h1 hne
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc, h3])

theorem exists_mem_scriptQPiStar_top (A : Subgroup G) :
    ∃ S, S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) := by
  have hbot : (⊥ : Subgroup G) ∈ scriptQPi A (lB A) ⊤ (piOf 2) := by
    refine ⟨⟨⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B _ => ?_⟩, bot_le⟩,
      (bot_mem_invariantPiSubgroups ⊤ A (piOf 2)).2.1⟩
    rw [bot_inf_eq]
    exact bot_le
  obtain ⟨S, -, hS⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf 2))) hbot
  exact ⟨S, hS⟩

theorem exists_card_nine_not_odd {A L : Subgroup G} {c : G} (h : Sec13Data G A c L)
    (hodd : ∀ a ∈ A, a ≠ 1 → Odd (Nat.card (⁅thetaCen ({a} : Set G), A⁆ : Subgroup G))) :
    ∃ E ≤ A, Nat.card E = 9 ∧ ¬ Odd (Nat.card (thetaT 3 E)) := by
  by_contra hn
  push Not at hn
  have hS : A ∈ partTwoS G := ⟨h.mem_partTwoF, hodd, fun B hBA hB9 => hn B hBA hB9⟩
  rw [h.partTwoS_eq] at hS
  simp at hS

omit [Finite G] in
theorem thetaT_le_thetaCen {E : Subgroup G} {e : G} (he : e ∈ E) (he1 : e ≠ 1) :
    thetaT 3 E ≤ thetaCen ({e} : Set G) :=
  iInf_le_of_le e (iInf_le_of_le he (iInf_le_of_le he1 le_rfl))

theorem le_centralizer_of_forall_ne_one {B S Z : Subgroup G}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : 9 ≤ Nat.card B)
    (hBS : B ≤ Subgroup.normalizer (S : Set G)) (hS : ¬ 3 ∣ Nat.card S)
    (h : ∀ b ∈ B, b ≠ 1 →
      S ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.centralizer (Z : Set G)) :
    S ≤ Subgroup.centralizer (Z : Set G) := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
    Nat.prime_three B S ⟨hB.1, hB.2⟩ (by norm_num; exact hB9) hBS
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hS)
  rw [← hgen]
  refine iSup_le fun D => iSup_le fun hD => ?_
  obtain ⟨hDB, hD3⟩ := hD
  have hDne : D ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hD3
    norm_num at hD3
  obtain ⟨⟨b, hbD⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
  have hb1' : b ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
  refine le_trans ?_ (h b (hDB hbD) hb1')
  exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbD))

end CFSG.RankThree.PartTwo.Sec16.Proof169

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem step1611_of (h1610 : Step1610) (h146 : Item146S14) (hbot : Item145BotS14)
    (h1411 : Item1411_3R) (h142 : Item142R) (hL : Step1611List) : Step1611 := by
  intro G _ _ A c L h
  by_contra hn
  have hNT := hL G A c L h.toSec15R (h142 G A c L h.toSec15R) hn
  have hS : Item1411_3Strong A (lB A) :=
    rank3II_14_11_3_strong_of h.isE27 (h146 G A c L h.toSec14Std)
      (hbot G A c L h.toSec14Std) (h1411 G A c L h.toSec15R)
  have hne := rank3II_16_9_1_of_not_transOn h.isElemAbelian.1 h.mem_A
    (fun _ => h1610 G A c L h) hS hNT
  rw [h.scriptY0_eq] at hne
  exact Set.not_nonempty_empty hne

theorem step1612_of (h1610 : Step1610) (hNS : Step1612NotSimple) (hY3 : Step1612Y3) :
    Step1612 := by
  intro G _ _ A c L h
  by_cases h34 : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2))
  · exact Or.inr h34
  rw [not_nonempty_iff] at h34
  refine Or.inl (by_contra fun hn => ?_)
  obtain ⟨T, hT, hT1⟩ : ∃ T ∈ invariantPiSubgroups ⊤ (A ⊔ L) (piOf 2), T ≠ ⊥ := by
    by_cases hsimp : IsSimpleGroup ↥L
    · have hex : ∃ T ∈ invariantPiSubgroups (Subgroup.centralizer (L : Set G)) A (piOf 2),
          T ≠ ⊥ := by
        by_contra hall
        push Not at hall
        exact hn ⟨hsimp, hall⟩
      obtain ⟨T, hT, hT1⟩ := hex
      have hLT : L ≤ Subgroup.normalizer (T : Set G) :=
        (Subgroup.le_centralizer_iff.mp hT.1).trans (Subgroup.centralizer_le_normalizer _)
      exact ⟨T, ⟨le_top, hT.2.1, sup_le hT.2.2 hLT⟩, hT1⟩
    · exact hNS G A c L h hsimp h34
  obtain ⟨Y, hY, hO⟩ := hY3 G A c L h h34 T hT hT1
  rw [h1610 G A c L h] at hY
  exact hO hY.2

section Item1616

theorem step1616_of (h1611 : Step1611) (h1614 : Step1614) (h1615 : Step1615)
    (hMeet : KS1615Meet) (hFix : Step1616Fix) (hComm : Step1616Comm) (hΩ : Step1616Omega) :
    Step1616 := by
  intro G _ _ A c L h
  rcases h1611 G A c L h with hPGL | h2
  swap
  · exact h2
  exfalso
  obtain ⟨hodd, hoddB⟩ := h1615 G A c L h hPGL
  set B := Subgroup.zpowers c ⊔ (A ⊓ L) with hB
  have hBA : B ≤ A := sup_le (Subgroup.zpowers_le.mpr h.mem_A) inf_le_left
  have hA27 : Nat.card A = 27 := h.card_eq
  have hcL : c ∉ L := h.toSec15R.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  have hB9 : 9 ≤ Nat.card B := by
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hMeet G A c L h hPGL)
    have hx1' : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
    have hxc : x ∉ Subgroup.zpowers c := by
      intro hxc
      have heq := zpowers_eq_of_mem_of_ne_one h.card_zpowers hxc hx1'
      apply hcL
      have hcx : c ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers c
      exact (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hx).2) hcx
    refine nine_le_card_of_lt hBA hA27 h.card_zpowers
      (lt_of_le_of_ne le_sup_left fun heq => hxc ?_)
    rw [heq]
    exact (le_sup_right : A ⊓ L ≤ B) hx
  obtain ⟨S, hS⟩ := exists_mem_scriptQPiStar_top A
  have hBS : B ≤ Subgroup.normalizer (S : Set G) := hBA.trans hS.prop.1.1.1.2.2
  have hS3 : ¬ 3 ∣ Nat.card S :=
    (isPiSubgroup_piCompl_iff Nat.prime_three S).mp hS.prop.1.1.1.2.1
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := isElemAbelian_of_le h.isElemAbelian hBA
  by_cases hSc : ⁅S, Subgroup.zpowers c⁆ = ⊥
  · rcases hFix G A c L h hPGL S hS hSc with hSA | hev
    · obtain ⟨E, hEA, hE9, hEev⟩ :=
        exists_card_nine_not_odd h.toSec13Data (hComm G A c L h S hS hSA)
      obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
        (inf_ne_bot_of_nine_le hBA hEA hA27 hB9 hE9.ge)
      have he1' : e ≠ 1 := fun h1 => he1 (Subtype.ext h1)
      exact hEev ((hodd e (Subgroup.mem_inf.mp he).1 he1').of_dvd_nat
        (Subgroup.card_dvd_of_le (thetaT_le_thetaCen (Subgroup.mem_inf.mp he).2 he1')))
    · exact hev hoddB
  · obtain ⟨b, hbB, hb1, hbT⟩ : ∃ b ∈ B, b ≠ 1 ∧
        ⁅S ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ ≠ ⊥ := by
      by_contra hall
      push Not at hall
      apply hSc
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact le_centralizer_of_forall_ne_one hBe hB9 hBS hS3 fun b hb hb1 =>
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hall b hb hb1)
    have hΩb := hΩ G A c L h hPGL S hS b hbB hb1 (hodd b hbB hb1) hbT
    rw [h1614 G A c L h, Set.mem_singleton_iff] at hΩb
    exact hbT (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (inf_le_right.trans (centralizer_le_of_zpowers_eq hΩb)))

end Item1616

end CFSG.RankThree.PartTwo.Sec16

namespace CFSG.RankThree.PartTwo.Sec16.Proof169

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem isoLThreePi_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {p k : ℕ}
    [Fact p.Prime] (h : Sec4.IsoLThreePi X p k) : Sec4.IsoLThreePi Y p k := by
  rcases h with ⟨h3, ⟨f⟩⟩ | ⟨h3, ⟨f⟩⟩
  · exact Or.inl ⟨h3, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨h3, ⟨e.symm.trans f⟩⟩

omit [Finite G] in
theorem three_dvd_card_of_j2 {K : Subgroup G}
    (hK : Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    3 ∣ Nat.card K := by
  obtain ⟨e⟩ := hK
  have h1 : Nat.card (↥K ⧸ aschbacherSolvableCore 3 ↥K) = 604800 := by
    rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_nativeJ2]
  have h2 := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥K)
  rw [h1] at h2
  exact (show 3 ∣ 604800 by norm_num).trans h2

omit [Finite G] in
theorem normalClosureSub_spec {O P : Subgroup G} (hPO : P ≤ O) :
    P ≤ normalClosureSub O P ∧ normalClosureSub O P ≤ O ∧
      O ≤ Subgroup.normalizer ((normalClosureSub O P : Subgroup G) : Set G) := by
  refine ⟨fun x hx => ⟨⟨x, hPO hx⟩, Subgroup.subset_normalClosure
    (Subgroup.mem_subgroupOf.mpr hx), rfl⟩, Subgroup.map_subtype_le _, ?_⟩
  intro o ho
  rw [Subgroup.mem_normalizer_iff]
  have hn := Subgroup.normalClosure_normal (s := ((P.subgroupOf O : Subgroup ↥O) : Set ↥O))
  intro y
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨o, ho⟩ * k * ⟨o, ho⟩⁻¹, hn.conj_mem k hk _, ?_⟩
    simp
  · rintro ⟨k, hk, hky⟩
    refine ⟨⟨o, ho⟩⁻¹ * k * ⟨o, ho⟩⁻¹⁻¹, hn.conj_mem k hk _, ?_⟩
    have hky' : (k : G) = o * y * o⁻¹ := hky
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, hky']
    group

end CFSG.RankThree.PartTwo.Sec16.Proof169

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.GH74.GLS
open scoped commutatorElement

section Item1618

theorem step1618_of (h1614 : Step1614) (h1617 : Step1617) (hT : Step1618Trans) :
    Step1618 := by
  intro G _ _ A c L h g hg
  by_contra hne
  set c' := g * c * g⁻¹ with hc'
  have hzc' : Subgroup.zpowers c' = (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hgH : g ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    intro hgH
    apply hne
    rw [hzc']
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hgH
  obtain ⟨h9, htr⟩ := hT G A c L h (h1617 G A c L h) g hgH hg
  have hWH : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    normalizer_le_of_omegaA_eq (h1614 G A c L h)
  have hcL : c ∉ L := h.toSec15R.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  set Lg := L.map (MulAut.conj g).toMonoidHom with hLg
  have hc'Lg : c' ∉ Lg := by
    rintro ⟨l, hl, hlc⟩
    apply hcL
    have hlc' : g * l * g⁻¹ = g * c * g⁻¹ := hlc
    have : l = c := mul_left_cancel (mul_right_cancel hlc')
    exact this ▸ hl
  have hLgC : Lg ≤ Subgroup.centralizer ({c'} : Set G) := by
    rintro _ ⟨l, hl, rfl⟩
    have hlc : l * c = c * l := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
    rw [Subgroup.mem_centralizer_singleton_iff]
    change g * l * g⁻¹ * (g * c * g⁻¹) = g * c * g⁻¹ * (g * l * g⁻¹)
    calc g * l * g⁻¹ * (g * c * g⁻¹) = g * (l * c) * g⁻¹ := by group
      _ = g * (c * l) * g⁻¹ := by rw [hlc]
      _ = g * c * g⁻¹ * (g * l * g⁻¹) := by group
  set B := Subgroup.zpowers c ⊔ Subgroup.zpowers c' with hB
  have hBA : B ≤ A := sup_le (Subgroup.zpowers_le.mpr h.mem_A) (Subgroup.zpowers_le.mpr hg)
  have hc'B : c' ∈ B := (le_sup_right : Subgroup.zpowers c' ≤ B) (Subgroup.mem_zpowers c')
  have hcard' : Nat.card (Subgroup.zpowers c') = 3 := by
    rw [hzc', Subgroup.card_map_of_injective (MulAut.conj g).injective, h.card_zpowers]
  have hc'c : c' ∉ Subgroup.zpowers c := by
    intro hmem
    apply hne
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem)
      (by rw [hcard', h.card_zpowers])
  have hB9 : 9 ≤ Nat.card B := nine_le_card_of_lt hBA h.card_eq h.card_zpowers
    (lt_of_le_of_ne le_sup_left fun heq => hc'c (heq ▸ hc'B))
  have hB9' : Nat.card B ≤ 9 :=
    card_sup_zpowers_le (h.commute h.mem_A hg) h.card_zpowers hcard'
  set D := A ⊓ Lg with hD
  have hBD : B ⊓ D ≠ ⊥ := inf_ne_bot_of_nine_le hBA inf_le_left h.card_eq hB9 h9.ge
  have hDB : ¬ D ≤ B := by
    intro hDB
    have hDeq : D = B := Subgroup.eq_of_le_of_card_ge hDB (by omega)
    have hc'D : c' ∈ D := hDeq ▸ hc'B
    exact hc'Lg (Subgroup.mem_inf.mp hc'D).2
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBD
  have hy1' : y ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
  obtain ⟨z, hzD, hzB⟩ := IsConcreteLE.not_le_iff_exists.mp hDB
  have hz1 : z ≠ 1 := fun h1 => hzB (h1 ▸ B.one_mem)
  obtain ⟨w, hw, hwyz⟩ := htr y (Subgroup.mem_inf.mp hy).2 hy1' z hzD hz1
  obtain ⟨hwW, hwLg⟩ := Subgroup.mem_inf.mp hw
  have hBw : B ≤ B.comap (MulAut.conj w).toMonoidHom := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · have hwc := (Subgroup.mem_normalizer_iff.mp (hWH hwW) c).mp (Subgroup.mem_zpowers c)
      exact (le_sup_left : Subgroup.zpowers c ≤ B) hwc
    · have hwc : w * c' = c' * w := Subgroup.mem_centralizer_singleton_iff.mp (hLgC hwLg)
      change w * c' * w⁻¹ ∈ B
      rw [hwc, mul_inv_cancel_right]
      exact hc'B
  have hwy : w * y * w⁻¹ ∈ B := hBw (Subgroup.mem_inf.mp hy).1
  exact hzB (hwyz ▸ hwy)

end Item1618

theorem step1621_of (h1616 : Step1616) (h1619 : Step1619) (hU38 : Step169U38)
    (hP : Para1619) (h1620 : Step1620) (hConj : Step1621Conj) : Step1621 := by
  intro G _ _ A c L h a ha ha1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := h1616 G A c L h
  obtain ⟨h34, hsolv⟩ := h1619 G A c L h
  obtain ⟨b, p, P, hD⟩ := hP G A c L h n hn h34 hsolv (hU38 G A c L h)
  by_contra hO
  obtain ⟨w, hwW, hwP⟩ := hConj G A c L h b n p P hD a ha ha1
  set C := CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({a} : Set G)) with hC
  have hCQ : C ∈ scriptQ A (lB A) := pCoreOf_two_mem_scriptQ h.isElemAbelian.1 ha
  have hY : delta A (lB A) (Subgroup.normalizer (C : Set G)) ∈ scriptY3 A (lB A) :=
    delta_normalizer_mem_scriptY3 h.isSimpleGroup h.nonabelian hO
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _) hCQ
  have hPQ : P ∈ scriptQ A (lB A) := hD.mem_Q.1.1
  have hPwQ : P.map (MulAut.conj w).toMonoidHom ∈ scriptQ A (lB A) :=
    rank3II_14_4_5 (isNaturalFamily_lB A) hwW hPQ
  have hPwN : P.map (MulAut.conj w).toMonoidHom ≤ Subgroup.normalizer (C : Set G) :=
    hwP.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hPwY := le_delta hPwQ hPwN
  have hY' := Sec17.HeadProof.map_conj_mem_scriptY3 (inv_mem hwW) hY
  have hPY' : P ≤ (delta A (lB A) (Subgroup.normalizer (C : Set G))).map
      (MulAut.conj w⁻¹).toMonoidHom := by
    have hm := Subgroup.map_mono (f := (MulAut.conj w⁻¹).toMonoidHom) hPwY
    rwa [Late.map_conj_map_conj, inv_mul_cancel, Late.map_conj_one] at hm
  have hP1 : P ≠ ⊥ := by
    intro hbot
    have hc := hD.card
    rw [hbot, Subgroup.card_bot] at hc
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hD.prime.one_lt
    omega
  exact h1620 G A c L h b n p P hD P ⟨hPQ, le_rfl⟩ hP1 _ hY' hPY'

end CFSG.RankThree.PartTwo.Sec16
