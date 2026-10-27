module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res4ProofNonsolv
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res5ProofPGL
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4 (InducesTypeOn)
open scoped commutatorElement

@[expose] noncomputable def Claim1411NonsolvWPointOutR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
      ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
        3 ∣ Nat.card Y →
        (∀ B, IsHyperplane A B → Y ≤ Subgroup.centralizer (B : Set G) → lB A B ≠ ⊥) →
        (∀ Y' ∈ scriptY A, Nat.card Y' < Nat.card Y →
          TransOn A (lB A) (Subgroup.normalizer (A : Set G)) Y') →
        ∀ S ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T ∈ scriptQPiStar A (lB A) Y (piOf 2),
          Y ≤ Subgroup.normalizer ((S ⊓ T : Subgroup G) : Set G) →
          (∀ S' ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T' ∈ scriptQPiStar A (lB A) Y (piOf 2),
            Nat.card (S ⊓ T : Subgroup G) < Nat.card (S' ⊓ T' : Subgroup G) →
              IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S' T') →
          (∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T → Y ≤ Subgroup.centralizer ({a} : Set G)) →
          ∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            (Subgroup.zpowers a ∈ omegaA A ∨
              delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ≠
                pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
                  pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) →
            (Subgroup.zpowers a ∈ omegaA A → ∀ La ∈ lA A a,
              ¬ Sec8.IsZ3PGLThreePi (lBarA a La A) ∧
                (Subgroup.zpowers a ∈ gammaA A (lB A) ∨
                  ∃ r ∈ xA A, ∃ l ∈ La, ⁅r, l⁆ ∉ inSubgroup (aschbacherSolvableCore 3) La)) →
            IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T

@[expose] noncomputable def Claim1411NonsolvXPointOutR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
      (∀ a : G, Subgroup.zpowers a ∈ omegaA A →
          TransOn A (lB A) (xA A) (Subgroup.centralizer ({a} : Set G))) →
      ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
        3 ∣ Nat.card Y →
        (∀ B, IsHyperplane A B → Y ≤ Subgroup.centralizer (B : Set G) → lB A B ≠ ⊥) →
        (∀ Y' ∈ scriptY A, Nat.card Y' < Nat.card Y → TransOn A (lB A) (xA A) Y') →
        ∀ S ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T ∈ scriptQPiStar A (lB A) Y (piOf 2),
          Y ≤ Subgroup.normalizer ((S ⊓ T : Subgroup G) : Set G) →
          (∀ S' ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T' ∈ scriptQPiStar A (lB A) Y (piOf 2),
            Nat.card (S ⊓ T : Subgroup G) < Nat.card (S' ⊓ T' : Subgroup G) →
              IsConjIn (xA A ⊓ Y) S' T') →
          (∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T → Y ≤ Subgroup.centralizer ({a} : Set G)) →
          ∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            (Subgroup.zpowers a ∈ omegaA A ∨
              delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ≠
                pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
                  pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) →
            (Subgroup.zpowers a ∈ omegaA A → ∀ La ∈ lA A a,
              ¬ Sec8.IsZ3PGLThreePi (lBarA a La A) ∧
                ∃ r ∈ xA A, ∃ l ∈ La, ⁅r, l⁆ ∉ inSubgroup (aschbacherSolvableCore 3) La) →
            IsConjIn (xA A ⊓ Y) S T

@[expose] noncomputable def Claim1411NonsolvXPointFR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      (∀ a : G, Subgroup.zpowers a ∈ omegaA A →
          TransOn A (lB A) (xA A) (Subgroup.centralizer ({a} : Set G))) →
      ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
        3 ∣ Nat.card Y →
        (∀ B, IsHyperplane A B → Y ≤ Subgroup.centralizer (B : Set G) → lB A B ≠ ⊥) →
        (∀ Y' ∈ scriptY A, Nat.card Y' < Nat.card Y → TransOn A (lB A) (xA A) Y') →
        ∀ S ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T ∈ scriptQPiStar A (lB A) Y (piOf 2),
          Y ≤ Subgroup.normalizer ((S ⊓ T : Subgroup G) : Set G) →
          (∀ S' ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T' ∈ scriptQPiStar A (lB A) Y (piOf 2),
            Nat.card (S ⊓ T : Subgroup G) < Nat.card (S' ⊓ T' : Subgroup G) →
              IsConjIn (xA A ⊓ Y) S' T') →
          (∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T → Y ≤ Subgroup.centralizer ({a} : Set G)) →
          ∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T → Subgroup.zpowers a ∈ omegaA A →
            ∀ La ∈ lA A a,
              IsEmpty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* CFSG.Blueprint.NativeSporadic.J2) →
              ¬ Sec8.IsZ3PGLThreePi (lBarA a La A) →
              (∃ r ∈ xA A, ∃ l ∈ La, ⁅r, l⁆ ∉ inSubgroup (aschbacherSolvableCore 3) La) →
              IsConjIn (xA A ⊓ Y) S T

@[expose] noncomputable def Claim1411NonsolvXCentFR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      (∀ a : G, Subgroup.zpowers a ∈ omegaA A →
          TransOn A (lB A) (xA A) (Subgroup.centralizer ({a} : Set G))) →
      ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
        3 ∣ Nat.card Y →
        (∀ B, IsHyperplane A B → Y ≤ Subgroup.centralizer (B : Set G) → lB A B ≠ ⊥) →
        (∀ Y' ∈ scriptY A, Nat.card Y' < Nat.card Y → TransOn A (lB A) (xA A) Y') →
        ∀ S ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T ∈ scriptQPiStar A (lB A) Y (piOf 2),
          Y ≤ Subgroup.normalizer ((S ⊓ T : Subgroup G) : Set G) →
          (∀ S' ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T' ∈ scriptQPiStar A (lB A) Y (piOf 2),
            Nat.card (S ⊓ T : Subgroup G) < Nat.card (S' ⊓ T' : Subgroup G) →
              IsConjIn (xA A ⊓ Y) S' T') →
          (∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T → Y ≤ Subgroup.centralizer ({a} : Set G)) →
          IsConjIn (xA A ⊓ Y) S T

namespace Proof1413Res5

variable {G : Type} [Group G] [Finite G]

theorem transOn_of_pgl_point
    (h131 : Item131) (h142 : Item142AllS14)
    (hbot : Item145BotS14) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L) {a : G}
    (ha : Subgroup.zpowers a ∈ omegaA A) {La : Subgroup G} (hLa : La ∈ lA A a)
    (hPGL : Sec8.IsZ3PGLThreePi (lBarA a La A)) {Y : Subgroup G}
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) :
    TransOn A (lB A) (xA A) Y := by
  have h' : Sec14Std G A a La := Proof1413.sec14Std_at hR.toSec14Std ha hLa
  obtain ⟨Y₀, hY₀q, -, hle⟩ := exists_mem_scriptQ_of_pgl sporadicModels131 h' hPGL
    (exists_type3_of_pgl h131 h'.toSec13Data hPGL) (h142 G A a La h')
  have hYH : Y ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) :=
    hYa.trans (centralizer_singleton_le_normalizer_zpowers a)
  have hY₀Y : Y₀ ⊓ Y ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hY₀q inf_le_left (le_normalizer_inf hY₀q.1.2.2 hAY)
  refine transOn_of_le_mem_scriptQ h'.isE27 (hbot G A a La h') hY₀Y inf_le_right
    fun R hR' => le_inf (hle R ⟨⟨hR'.1.1, hR'.1.2.trans hYH⟩, hR'.2⟩) hR'.1.2

theorem transOn_centralizer_of_not_mem_gammaA {A : Subgroup G} (hA : IsE27 A) {a : G}
    (ha : Subgroup.zpowers a ∈ omegaA A) (hΓ : Subgroup.zpowers a ∉ gammaA A (lB A)) :
    TransOn A (lB A) (xA A) (Subgroup.centralizer ({a} : Set G)) := by
  have haA : a ∈ A := (zpowers_mem_omegaA_iff.mp ha).1
  have htr : TransOn A (lB A) (xA A) (Subgroup.normalizer (Subgroup.zpowers a : Set G)) := by
    by_contra hno
    exact hΓ ⟨ha, hno⟩
  have hCN := centralizer_singleton_le_normalizer_zpowers a
  have hsub : ∀ S ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf 2),
      S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers a : Set G)) (piOf 2) := by
    intro S hS
    refine ⟨⟨⟨hS.prop.1.1, hS.prop.1.2.trans hCN⟩, hS.prop.2⟩, fun U hU hSU => ?_⟩
    exact hS.2 ⟨⟨hU.1.1, le_centralizer_of_le_normalizer_zpowers hA haA hU.1.1 hU.1.2⟩, hU.2⟩
      hSU
  have hXa : xA A ≤ Subgroup.centralizer ({a} : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))
  intro S hS T hT
  obtain ⟨x, hx, hxT⟩ := htr S (hsub S hS) T (hsub T hT)
  exact ⟨x, ⟨(Subgroup.mem_inf.mp hx).1, hXa (Subgroup.mem_inf.mp hx).1⟩, hxT⟩

theorem isConjIn_of_inner_point (h142 : Item142AllS14) (hbot : Item145BotS14)
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L) {a : G}
    (ha : Subgroup.zpowers a ∈ omegaA A) {La : Subgroup G} (hLa : La ∈ lA A a)
    (hcent : ∀ r ∈ xA A, ∀ l ∈ La, ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) La)
    (hloc : TransOn A (lB A) (xA A) (Subgroup.centralizer ({a} : Set G)))
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) {S T : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2)) (hT : T ∈ scriptQPiStar A (lB A) Y (piOf 2)) :
    IsConjIn (xA A ⊓ Y) S T := by
  have h' : Sec14Std G A a La := Proof1413.sec14Std_at hR.toSec14Std ha hLa
  have hD := h'.toSec13Data
  have := ker142_normal (LB := lB A) hD.isElemAbelian.1 hD.mem_A
  set H := Subgroup.normalizer (Subgroup.zpowers a : Set G) with hH
  set K := k142 A (lB A) a with hKdef
  have hCH : Subgroup.centralizer ({a} : Set G) ≤ H := centralizer_singleton_le_normalizer_zpowers a
  have h142' : ∀ Q ∈ maxInvariantPiSubgroups H A (piCompl 3),
      Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer ({a} : Set G)) ∧ _ :=
    h142 G A a La h'
  have hle_K : ∀ U ∈ scriptQ A (lB A), U ≤ Subgroup.centralizer ({a} : Set G) → U ≤ K :=
    fun U hU hUa => le_delta hU (hUa.trans hCH)
  have hSY : S ≤ Y := hS.prop.1.2
  have hTY : T ≤ Y := hT.prop.1.2
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  suffices hZ : ∃ Z ∈ scriptQ A (lB A), S ≤ Z ∧ T ≤ Z by
    obtain ⟨Z, hZq, hSZ, hTZ⟩ := hZ
    have hZY : Z ⊓ Y ∈ scriptQ A (lB A) :=
      mem_scriptQ_of_le hZq inf_le_left (le_normalizer_inf hZq.1.2.2 hAY)
    exact isConjIn_of_le_mem_scriptQ h'.isE27 (hbot G A a La h') hZY inf_le_right hS hT
      (le_inf hSZ hSY) (le_inf hTZ hTY)
  obtain ⟨Q₀, hQ₀⟩ := maxInvariantPiSubgroups_nonempty H A (piCompl 3)
  obtain ⟨hQ₀q, hQ₀b⟩ := h142' Q₀ hQ₀
  rcases hQ₀b with ⟨-, hQK, -, -⟩ | ⟨hK, -⟩
  ·
    refine ⟨K, ?_, hle_K S hS.prop.1.1 (hSY.trans hYa), hle_K T hT.prop.1.1 (hTY.trans hYa)⟩
    rw [hKdef, ← hQK]
    exact hQ₀q.1
  ·
    have P : Pt142 A a La := ⟨h', hK⟩
    have hXO := P.xA_le_pCore hcent
    obtain ⟨S', hSS', hS'⟩ := Finite.exists_le_maximal
      (p := (· ∈ scriptQPi A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf 2))) (a := S)
      ⟨⟨hS.prop.1.1, hSY.trans hYa⟩, hS.prop.2⟩
    obtain ⟨T', hTT', hT'⟩ := Finite.exists_le_maximal
      (p := (· ∈ scriptQPi A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf 2))) (a := T)
      ⟨⟨hT.prop.1.1, hTY.trans hYa⟩, hT.prop.2⟩
    obtain ⟨x, hx, hxT'⟩ := hloc S' hS' T' hT'
    set Z := S' ⊔ pPrimeCoreOf 3 K with hZdef
    have hS'K : S' ≤ K := hle_K S' hS'.prop.1.1 hS'.prop.1.2
    have hxZ : x ∈ Z := Subgroup.mem_sup_right (hXO (Subgroup.mem_inf.mp hx).1)
    have hT'Z : T' ≤ Z := by
      rw [hxT', ← Late.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hxZ)]
      exact Subgroup.map_mono le_sup_left
    have hZ3 : IsPiSubgroup (piCompl 3) Z :=
      isPiSubgroup_piCompl_sup (isPiSubgroup_piCompl_three_of_piOf_two hS'.prop.2)
        ((isPiSubgroup_piCompl_iff Nat.prime_three _).mpr (not_three_dvd_pCoreOf _))
        (hS'K.trans (le_normalizer_pPrimeCoreOf 3 K))
    have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
      le_normalizer_sup hS'.prop.1.1.1.2.2
        (hAK.trans (normalizer_le_normalizer_pPrimeCoreOf 3 K))
    have hZH : Z ≤ H :=
      sup_le (hS'.prop.1.2.trans hCH) ((pPrimeCoreOf_le 3 K).trans (delta_le _))
    obtain ⟨Q', hQ', hZQ'⟩ := exists_le_mem_maxInvariantPiSubgroups ⟨hZH, hZ3, hAZ⟩
    exact ⟨Z, mem_scriptQ_of_le (h142' Q' hQ').1.1 hZQ' hAZ, hSS'.trans le_sup_left,
      hTT'.trans hT'Z⟩

end Proof1413Res5

open Proof1413Res5 in
theorem claim1411NonsolvWPointR_of_out
    (h131 : Item131)
    (h142 : Item142AllS14) (hbot : Item145BotS14) (h : Claim1411NonsolvWPointOutR) :
    Claim1411NonsolvWPointR := by
  intro G _ _ A c L hR Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT hpt
  have hYa := hres a haA ha1 haS haT
  have hXW : xA A ≤ Subgroup.normalizer (A : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)
  by_cases hset : Subgroup.zpowers a ∈ omegaA A ∧ ∃ La ∈ lA A a,
      Sec8.IsZ3PGLThreePi (lBarA a La A) ∨
        (Subgroup.zpowers a ∉ gammaA A (lB A) ∧
          ∀ r ∈ xA A, ∀ l ∈ La, ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) La)
  · obtain ⟨ha, La, hLa, hPGL | ⟨hΓ, hcent⟩⟩ := hset
    · exact (transOn_of_pgl_point h131 h142 hbot hR ha hLa hPGL hY.2 hYa S hS T hT).mono
        (inf_le_inf_right Y hXW)
    · exact (isConjIn_of_inner_point h142 hbot hR ha hLa hcent
        (transOn_centralizer_of_not_mem_gammaA hR.toSec14Std.isE27 ha hΓ) hY.2 hYa hS
        hT).mono (inf_le_inf_right Y hXW)
  · refine h G A c L hR Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT hpt
      fun ha La hLa => ⟨fun hPGL => hset ⟨ha, La, hLa, Or.inl hPGL⟩, ?_⟩
    by_contra hno
    push Not at hno
    exact hset ⟨ha, La, hLa, Or.inr hno⟩

open Proof1413Res5 in
theorem claim1411NonsolvXPointR_of_out
    (h131 : Item131)
    (h142 : Item142AllS14) (hbot : Item145BotS14) (h : Claim1411NonsolvXPointOutR) :
    Claim1411NonsolvXPointR := by
  intro G _ _ A c L hR hloc Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT
    hpt
  have hYa := hres a haA ha1 haS haT
  by_cases hset : Subgroup.zpowers a ∈ omegaA A ∧ ∃ La ∈ lA A a,
      Sec8.IsZ3PGLThreePi (lBarA a La A) ∨
        ∀ r ∈ xA A, ∀ l ∈ La, ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) La
  · obtain ⟨ha, La, hLa, hPGL | hcent⟩ := hset
    · exact transOn_of_pgl_point h131 h142 hbot hR ha hLa hPGL hY.2 hYa S hS T hT
    · exact isConjIn_of_inner_point h142 hbot hR ha hLa hcent (hloc a ha) hY.2 hYa hS hT
  · refine h G A c L hR hloc Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT
      hpt fun ha La hLa => ⟨fun hPGL => hset ⟨ha, La, hLa, Or.inl hPGL⟩, ?_⟩
    by_contra hno
    push Not at hno
    exact hset ⟨ha, La, hLa, Or.inr hno⟩

theorem claim1411NonsolvXR_of_out
    (h131 : Item131) (h142 : Item142AllS14)
    (h146 : Item146S14) (hbot : Item145BotS14) (h : Claim1411NonsolvXPointOutR) :
    Claim1411NonsolvXR :=
  claim1411NonsolvXR_of_point h146 hbot (claim1411NonsolvXPointR_of_out h131 h142 hbot h)

theorem claim1411NonsolvWR_of_out
    (h131 : Item131) (h142 : Item142AllS14)
    (h146 : Item146S14) (hbot : Item145BotS14) (h : Claim1411NonsolvWPointOutR) :
    Claim1411NonsolvWR :=
  claim1411NonsolvWR_of_point h146 hbot (claim1411NonsolvWPointR_of_out h131 h142 hbot h)

end CFSG.RankThree.PartTwo.Sec14
