module

public import CFSG.RankThree.PartTwo.Sec16.Item166ThreeStep5
public import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofStar
import CFSG.RankThree.PartTwo.Sec16.Item166ThreeOne
import CFSG.RankThree.PartTwo.Sec16.Item166ThreeSix
import CFSG.GH74.GLS.Balance.Bender.AuxSylow
import CFSG.RankThree.PartTwo.Sec17.Item17Res14ProofKb

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof166Three

open CFSG CFSG.Open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec17

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

private noncomputable def key (Z : Subgroup G) : ℕ ×ₗ ℕ :=
  toLex (Nat.card ↥(sSup (thetaComponentsIn Z)),
    (Nat.card ↥(perpOf Z (sSup (thetaComponentsIn Z)))).factorization 2)

private theorem exists_max_key {Z : Subgroup G} (hZ : Z ∈ scriptY3Star A (lB A))
    (hZ3 : ¬ 3 ∣ Nat.card Z) (hZns : ¬ Group.IsSolvable ↥Z)
    (hZM : ¬ Z ≤ Subgroup.normalizer (Y₀ : Set G)) :
    ∃ Z₁ ∈ scriptY3Star A (lB A), ¬ 3 ∣ Nat.card Z₁ ∧ ¬ Group.IsSolvable ↥Z₁ ∧
      ¬ Z₁ ≤ Subgroup.normalizer (Y₀ : Set G) ∧
        ∀ Z' ∈ scriptY3Star A (lB A), ¬ 3 ∣ Nat.card Z' → ¬ Group.IsSolvable ↥Z' →
          ¬ Z' ≤ Subgroup.normalizer (Y₀ : Set G) → key Z' ≤ key Z₁ := by
  classical
  let F : Set (Subgroup G) := {Z' | Z' ∈ scriptY3Star A (lB A) ∧ ¬ 3 ∣ Nat.card Z' ∧
    ¬ Group.IsSolvable ↥Z' ∧ ¬ Z' ≤ Subgroup.normalizer (Y₀ : Set G)}
  have hF : F.Nonempty := ⟨Z, hZ, hZ3, hZns, hZM⟩
  obtain ⟨Z₁, hZ₁, hmax⟩ := Set.exists_max_image F key (Set.toFinite F) hF
  exact ⟨Z₁, hZ₁.1, hZ₁.2.1, hZ₁.2.2.1, hZ₁.2.2.2,
    fun Z' hZ' h3 hns hM => hmax Z' ⟨hZ', h3, hns, hM⟩⟩

private theorem step6_final (h : Sec17Std G A c L Y₀) {Z₁ E : Subgroup G}
    (hZ₁M : ¬ Z₁ ≤ Subgroup.normalizer (Y₀ : Set G))
    (hEZ : E ≤ Z₁) (hZE : Z₁ ≤ Subgroup.normalizer (E : Set G))
    (hAE : A ≤ Subgroup.normalizer (E : Set G)) (hE3 : ¬ 3 ∣ Nat.card E)
    (hE2 : 2 ∣ Nat.card E) (hEperf : Group.IsPerfect ↥E)
    (hEC : (E : Set G) ⊆ Late.sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
      (CFSG.Open.pCoreOf 2 Y₀))
    (hcomp : ∃ S Z' : Subgroup G,
      S ≤ perpOf Z₁ E ∧ IsPGroup 2 S ∧ ¬ 2 ∣ S.relIndex (perpOf Z₁ E) ∧
        A ≤ Subgroup.normalizer (S : Set G) ∧
        S ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₀ : Set G) ∧
        Z' ∈ scriptY3Star A (lB A) ∧ ¬ 3 ∣ Nat.card Z' ∧
        ¬ Z' ≤ Subgroup.normalizer (Y₀ : Set G) ∧ E ≤ Z' ∧ S ≤ Z' ∧
        CFSG.Open.pCoreOf 2 Y₀ ⊓ Subgroup.normalizer (S : Set G) ≤ Z' ∧
        E = (sSup (thetaComponentsIn Z') : Subgroup G) ∧
        (Nat.card ↥(perpOf Z' E)).factorization 2 ≤
          (Nat.card ↥(perpOf Z₁ E)).factorization 2) : False := by
  classical
  obtain ⟨S, Z', hSle, hS2, hSyl, hAS, hSNQ, hZ', hZ'3, hZ'M, hEZZ', hSZ', hTZ', hEeq, hv⟩ :=
    hcomp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  set Q₀ := CFSG.Open.pCoreOf 2 Y₀ with hQ₀
  have hEM : E ≤ M := fun x hx => (hEC hx).1
  have hENQ : E ≤ Subgroup.normalizer (Q₀ : Set G) :=
    hEM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) Y₀)
  set T := Q₀ ⊓ Subgroup.normalizer (S : Set G) with hT
  have hT2 : IsPGroup 2 T := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀).to_inf_left
  have hTN : T ≤ Subgroup.normalizer (S : Set G) := inf_le_right
  have hTE : T ≤ Subgroup.normalizer (E : Set G) := by
    rw [hEeq]
    exact hTZ'.trans (le_normalizer_sSup_thetaComponentsIn Z')
  have hTperp : T ≤ perpOf Z' E :=
    le_perpOf_of_le_of_isPGroup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀) hENQ hTZ' hTE
      inf_le_left
  have hSperp : S ≤ perpOf Z' E := (le_inf hSle hSZ').trans (perpOf_inf_le Z₁ Z' E)
  have hR2 : IsPGroup 2 ↥(S ⊔ T) := hS2.to_sup_of_normal_left' hT2 hTN
  have hRperp : S ⊔ T ≤ perpOf Z' E := sup_le hSperp hTperp
  have hRcard : Nat.card ↥(S ⊔ T) ≤ Nat.card ↥S :=
    card_le_of_factorization_le (p := 2) (S := S) (P := perpOf Z₁ E) (R := S ⊔ T)
      (P' := perpOf Z' E) hSle hS2 hSyl hRperp hR2 hv
  have hsup : S ⊔ T = S :=
    (Subgroup.eq_of_le_of_card_ge (H := S) (K := S ⊔ T) le_sup_left hRcard).symm
  have hTle : T ≤ S := by rw [← hsup]; exact le_sup_right
  have hQleS : Q₀ ≤ S :=
    CFSG.GH74.GLS.Balance.le_of_inf_normalizer_le hS2
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀) hSNQ hTle
  have hQNE : Q₀ ≤ Subgroup.normalizer (E : Set G) :=
    hQleS.trans (hSle.trans (perpOf_le_normalizer Z₁ E))
  exact hZ₁M (le_M_of_le_normalizer h hEZ hZE hAE hE3 hE2 hEperf hEC hQNE)

section Certified


private theorem step6_facts (h : Sec17Std G A c L Y₀) (hgen : Gen166 A c)
    (hnosz : NoSz166 Y₀) {Z E : Subgroup G} (hE : E = sSup (thetaComponentsIn Z))
    (hZ : Z ∈ scriptY3 A (lB A)) (hZ3 : ¬ 3 ∣ Nat.card Z)
    (hZns : ¬ Group.IsSolvable ↥Z) :
    E ≤ Z ∧ Z ≤ Subgroup.normalizer (E : Set G) ∧
      A ≤ Subgroup.normalizer (E : Set G) ∧ Group.IsPerfect ↥E ∧
      ¬ 3 ∣ Nat.card E ∧ 2 ∣ Nat.card E ∧ ¬ Group.IsSolvable ↥E ∧
      ((E : Set G) ⊆ Late.sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
        (CFSG.Open.pCoreOf 2 Y₀)) ∧
      E ≤ Subgroup.normalizer (Y₀ : Set G) ∧
      E ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₀ : Set G) := by
  subst hE
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) := hZ.1.1.2
  have hEZ : (sSup (thetaComponentsIn Z) : Subgroup G) ≤ Z := sSup_thetaComponentsIn_le Z
  have hZE : Z ≤ Subgroup.normalizer ((sSup (thetaComponentsIn Z) : Subgroup G) : Set G) :=
    le_normalizer_sSup_thetaComponentsIn Z
  have hAE : A ≤ Subgroup.normalizer ((sSup (thetaComponentsIn Z) : Subgroup G) : Set G) :=
    hAZ.trans (normalizer_le_normalizer_sSup_thetaComponentsIn Z)
  have hEperf : Group.IsPerfect ↥((sSup (thetaComponentsIn Z) : Subgroup G)) :=
    isPerfect_sSup_thetaComponentsIn Z
  have hE3 : ¬ 3 ∣ Nat.card ↥((sSup (thetaComponentsIn Z) : Subgroup G)) :=
    not_three_dvd_sSup_thetaComponentsIn (Z := Z) hZ3
  obtain ⟨hEns, hE2⟩ := not_isSolvable_sSup_of_three h hZ hZ3 hZns
  have hEC : (((sSup (thetaComponentsIn Z) : Subgroup G)) : Set G) ⊆
      Late.sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
        (CFSG.Open.pCoreOf 2 Y₀) := sSup_subset_sectionCentralizer h hgen hnosz hZ hZ3
  have hEM : (sSup (thetaComponentsIn Z) : Subgroup G) ≤ Subgroup.normalizer (Y₀ : Set G) :=
    fun x hx => (hEC hx).1
  have hENQ : (sSup (thetaComponentsIn Z) : Subgroup G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₀ : Set G) :=
    hEM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) Y₀)
  exact ⟨hEZ, hZE, hAE, hEperf, hE3, hE2, hEns, hEC, hEM, hENQ⟩

private theorem step6_comp (h : Sec17Std G A c L Y₀) (hgen : Gen166 A c)
    (hnosz : NoSz166 Y₀) (h146 : Item146 A (lB A)) (h149 : Item149 A (lB A))
    (hQ0 : CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A)) (hne : OmegaNe166 A Y₀)
    {Z₁ E : Subgroup G} (hE : E = sSup (thetaComponentsIn Z₁))
    (hZ₁ : Z₁ ∈ scriptY3Star A (lB A)) (hZ₁3 : ¬ 3 ∣ Nat.card Z₁)
    (hZ₁ns : ¬ Group.IsSolvable ↥Z₁) (hZ₁M : ¬ Z₁ ≤ Subgroup.normalizer (Y₀ : Set G))
    (hmax : ∀ Z' ∈ scriptY3Star A (lB A), ¬ 3 ∣ Nat.card Z' → ¬ Group.IsSolvable ↥Z' →
      ¬ Z' ≤ Subgroup.normalizer (Y₀ : Set G) → key Z' ≤ key Z₁)
    (hAE : A ≤ Subgroup.normalizer (E : Set G)) (hEperf : Group.IsPerfect ↥E)
    (hEns : ¬ Group.IsSolvable ↥E) :
    ∃ S Z' : Subgroup G,
      S ≤ perpOf Z₁ E ∧ IsPGroup 2 S ∧ ¬ 2 ∣ S.relIndex (perpOf Z₁ E) ∧
        A ≤ Subgroup.normalizer (S : Set G) ∧
        S ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₀ : Set G) ∧
        Z' ∈ scriptY3Star A (lB A) ∧ ¬ 3 ∣ Nat.card Z' ∧
        ¬ Z' ≤ Subgroup.normalizer (Y₀ : Set G) ∧ E ≤ Z' ∧ S ≤ Z' ∧
        CFSG.Open.pCoreOf 2 Y₀ ⊓ Subgroup.normalizer (S : Set G) ≤ Z' ∧
        E = (sSup (thetaComponentsIn Z') : Subgroup G) ∧
        (Nat.card ↥(perpOf Z' E)).factorization 2 ≤
          (Nat.card ↥(perpOf Z₁ E)).factorization 2 := by
  classical
  subst hE
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ₁' : Z₁ ∈ scriptY3 A (lB A) := hZ₁.prop
  have hAZ : A ≤ Subgroup.normalizer (Z₁ : Set G) := hZ₁.prop.1.1.2
  obtain ⟨S, hSle, hS2, hSyl, hAS⟩ :=
    exists_sylow_perpOf (A := A) (Z := Z₁) (E := sSup (thetaComponentsIn Z₁))
      (HeadProof.isE27_of_std h).isPGroup hZ₁3 hAZ hAE
  have hSZ : S ≤ Z₁ := hSle.trans (perpOf_le Z₁ (sSup (thetaComponentsIn Z₁)))
  have hSM : S ≤ Subgroup.normalizer (Y₀ : Set G) :=
    le_M_of_isPGroup_two h h146 hZ₁' hZ₁3 hSZ hS2 hAS
  have hSNQ : S ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₀ : Set G) :=
    hSM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) Y₀)
  obtain ⟨Z', hZ', hZ'3, hZ'M, hEZZ', hSZ', hTZ'⟩ :=
    exists_container h hgen hnosz h146 h149 hQ0 hne (Z := Z₁) (S := S) hZ₁ hZ₁3 hZ₁ns hZ₁M
      hSle hS2 hSyl hAS
  have hZ'ns : ¬ Group.IsSolvable ↥Z' := by
    intro hs
    haveI := hs
    exact hEns (Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hEZZ') (Subgroup.inclusion_injective hEZZ'))
  have hEE' : (sSup (thetaComponentsIn Z₁) : Subgroup G) ≤
      (sSup (thetaComponentsIn Z') : Subgroup G) :=
    le_sSup_of_isPerfect_of_three h hZ'.prop hZ'3 hEZZ' hEperf
  have hkey := hmax Z' hZ' hZ'3 hZ'ns hZ'M
  have hcard : Nat.card ↥(sSup (thetaComponentsIn Z') : Subgroup G) ≤
      Nat.card ↥(sSup (thetaComponentsIn Z₁) : Subgroup G) := by
    simpa only [key, ofLex_toLex] using Prod.Lex.monotone_fst (key Z') (key Z₁) hkey
  have hEeq : (sSup (thetaComponentsIn Z₁) : Subgroup G) =
      (sSup (thetaComponentsIn Z') : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hEE' hcard
  have hv : (Nat.card ↥(perpOf Z' (sSup (thetaComponentsIn Z₁) : Subgroup G))).factorization 2 ≤
      (Nat.card ↥(perpOf Z₁ (sSup (thetaComponentsIn Z₁) : Subgroup G))).factorization 2 := by
    have hk : toLex (Nat.card ↥(sSup (thetaComponentsIn Z') : Subgroup G),
        (Nat.card ↥(perpOf Z' (sSup (thetaComponentsIn Z') : Subgroup G))).factorization 2) ≤
        toLex (Nat.card ↥(sSup (thetaComponentsIn Z₁) : Subgroup G),
          (Nat.card ↥(perpOf Z₁ (sSup (thetaComponentsIn Z₁) : Subgroup G))).factorization 2) :=
      hkey
    rw [← hEeq] at hk
    rcases Prod.Lex.toLex_le_toLex.mp hk with hlt | ⟨-, hle⟩
    · exact absurd hlt (lt_irrefl _)
    · exact hle
  exact ⟨S, Z', hSle, hS2, hSyl, hAS, hSNQ, hZ', hZ'3, hZ'M, hEZZ', hSZ', hTZ', hEeq, hv⟩

private theorem step6_contradiction (h : Sec17Std G A c L Y₀) (hgen : Gen166 A c)
    (hnosz : NoSz166 Y₀) (h146 : Item146 A (lB A)) (h149 : Item149 A (lB A))
    (hQ0 : CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A)) (hne : OmegaNe166 A Y₀)
    {Z₁ : Subgroup G} (hZ₁ : Z₁ ∈ scriptY3Star A (lB A)) (hZ₁3 : ¬ 3 ∣ Nat.card Z₁)
    (hZ₁ns : ¬ Group.IsSolvable ↥Z₁) (hZ₁M : ¬ Z₁ ≤ Subgroup.normalizer (Y₀ : Set G))
    (hmax : ∀ Z' ∈ scriptY3Star A (lB A), ¬ 3 ∣ Nat.card Z' → ¬ Group.IsSolvable ↥Z' →
      ¬ Z' ≤ Subgroup.normalizer (Y₀ : Set G) → key Z' ≤ key Z₁) : False := by
  classical
  set E := (sSup (thetaComponentsIn Z₁) : Subgroup G) with hE
  obtain ⟨hEZ, hZE, hAE, hEperf, hE3, hE2, hEns, hEC, _, _⟩ :=
    step6_facts h hgen hnosz hE hZ₁.prop hZ₁3 hZ₁ns
  exact step6_final h hZ₁M hEZ hZE hAE hE3 hE2 hEperf hEC
    (step6_comp h hgen hnosz h146 h149 hQ0 hne hE hZ₁ hZ₁3 hZ₁ns hZ₁M hmax hAE hEperf hEns)

theorem le_M_of_three (h : Sec17Std G A c L Y₀) (hgen : Gen166 A c) (hnosz : NoSz166 Y₀)
    (h146 : Item146 A (lB A)) (h149 : Item149 A (lB A))
    (hQ0 : CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A)) (hne : OmegaNe166 A Y₀)
    {Z : Subgroup G} (hZ : Z ∈ scriptY3Star A (lB A)) (hZ3 : ¬ 3 ∣ Nat.card Z)
    (hZns : ¬ Group.IsSolvable ↥Z) : Z ≤ Subgroup.normalizer (Y₀ : Set G) := by
  by_contra hZM
  obtain ⟨Z₁, hZ₁, hZ₁3, hZ₁ns, hZ₁M, hmax⟩ := exists_max_key hZ hZ3 hZns hZM
  exact step6_contradiction h hgen hnosz h146 h149 hQ0 hne hZ₁ hZ₁3 hZ₁ns hZ₁M hmax

theorem omega166Three_of_ne (h : Sec17Std G A c L Y₀) (hgen : Gen166 A c)
    (hnosz : NoSz166 Y₀) (h146 : Item146 A (lB A)) (h149 : Item149 A (lB A))
    (hQ0 : CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A)) (hne : OmegaNe166 A Y₀) :
    Omega166Three A Y₀ := by
  intro K₀ Z hK₀ hSz hK₀Z hZ hO
  have hZ3 : ¬ 3 ∣ Nat.card Z := Sec14.not_three_dvd_of_oPrimeResidualOf_eq_bot hO
  obtain ⟨m, hm⟩ := hSz
  have hK₀ns : ¬ Group.IsSolvable ↥K₀ :=
    Proof17Res14.not_isSolvable_of_suzukiModel_quot (CFSG.pCore 2 ↥K₀) hm
  have hZns : ¬ Group.IsSolvable ↥Z := by
    intro hs
    haveI := hs
    exact hK₀ns (Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hK₀Z) (Subgroup.inclusion_injective hK₀Z))
  exact le_M_of_three h hgen hnosz h146 h149 hQ0 hne hZ hZ3 hZns

end Certified

theorem omegaNe166_of_omg (h : Sec17Std G A c L Y₀) (hY4 : Step1610Y4Star A (lB A))
    (h152 : Item152 A (lB A)) (h155 : Item155 A (lB A)) (hΩ : Omg166Sz A Y₀) :
    OmegaNe166 A Y₀ := by
  intro K₀ Z hK₀ hSz hK₀Z hZ hO
  by_contra hZM
  obtain ⟨X', hX'4, hX'Z⟩ := hY4 Z hZ hO
  exact hZM (Proof166Res3.le_M_of_omg h h152 h155 hZ.prop hX'4 hX'Z
    (hΩ K₀ Z hK₀ hSz hK₀Z hZ hO hZM X' hX'4 hX'Z))

end CFSG.RankThree.PartTwo.Sec16.Proof166Three
