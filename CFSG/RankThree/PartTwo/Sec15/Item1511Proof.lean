module

public import CFSG.RankThree.PartTwo.Sec15.Item1511ProofTools
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute
import CFSG.RankThree.PartTwo.Sec15.Item1511Meta

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.Proof1511
open CFSG.Assembly.RankThreeEven (projSL projSU)

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Item158Y0 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)
    (L : Subgroup G) : Prop :=
  ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
    ∀ Y ∈ scriptY0 A LB, MeetsY4 A LB L Y →
    ∀ P : Subgroup G, A ≤ P →
      CFSG.ABGLocalTools.IsSylowOf 3 P
        (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)) →
      (Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
          A = omegaOneThree P) ∨
        (Sec14.IsZ3PGLThreeAt ↥(lBarA c L (omegaOneThree P)) p e ∧
          (Nat.card ↥(omegaOneThree P ⊔ L)).factorization 3 = 4 ∧
          (Nat.card ↥((omegaOneThree P ⊔ L) ⊓ Subgroup.normalizer (Y : Set G))).factorization 3 =
            4 ∧
          ∀ F : Subgroup G,
            CFSG.ABGLocalTools.IsSylowOf 3 F (Subgroup.zpowers c ⊔ L) →
              F ∈ partTwoF G ∧
                omegaA F = orbitIn (Subgroup.normalizer (F : Set G)) (Subgroup.zpowers c) ∧
                (omegaA F).ncard = 9)

end Defs

@[expose] noncomputable def Item158Y0R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Item158Y0 A (lB A) c L

section Star

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Item1511Star (A : Subgroup G) (LB : Subgroup G → Subgroup G)
    (c : G) (L : Subgroup G) : Prop :=
  ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
    ∀ Y ∈ scriptY0Star A LB, MeetsY4 A LB L Y →
    ∀ P : Subgroup G, A ≤ P →
      CFSG.ABGLocalTools.IsSylowOf 3 P
        (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)) →
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
        Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y ∧
        ((∃ n f : ℕ, 1 ≤ f ∧ e = n * f ∧ Sec14.IsLThreeEpsAt (↥Y ⧸ CFSG.pCore 2 ↥Y) p f) ∨
          Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))) ∧
        A = omegaOneThree P

omit [Finite G] in
theorem item1511Star_of_item1511 {A : Subgroup G} {LB : Subgroup G → Subgroup G} {c : G}
    {L : Subgroup G} (h : Item1511 A LB c L) : Item1511Star A LB c L :=
  fun p e _ he hL Y hY hmeet P hAP hP =>
    h p e he hL Y (scriptY0Star_subset A LB hY) hmeet P hAP hP

end Star

@[expose] noncomputable def Item1511StarR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Item1511Star A (lB A) c L

theorem item1511StarR_of_item1511R (h : Item1511R) : Item1511StarR :=
  fun G _ _ A c L hR => item1511Star_of_item1511 (h G A c L hR)

@[expose] noncomputable def Step1511List : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
    ∀ Y ∈ scriptY0 A (lB A), MeetsY4 A (lB A) L Y →
    ∀ P : Subgroup G, A ≤ P →
      CFSG.ABGLocalTools.IsSylowOf 3 P
        (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)) →
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      A = omegaOneThree P →
        Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y ∧
          ((∃ n f : ℕ, 1 ≤ f ∧ e = n * f ∧ Sec14.IsLThreeEpsAt (↥Y ⧸ CFSG.pCore 2 ↥Y) p f) ∨
            Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)))

section Proof

variable {G : Type} [Group G] [Finite G]

namespace Proof1511

theorem false_of_sylow (hset : Item13SetupAt) (h133 : Item133) (h159 : Item159R)
    (h1510 : Sec15.Item1510R) (hBr : Sec16.Step169TwoBridge) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) {p e : ℕ} [Fact p.Prime]
    (hL3 : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e) {F : Subgroup G}
    (hFL : F ≤ Subgroup.zpowers c ⊔ L) (hF : F ∈ partTwoF G)
    (hΩ : omegaA F = orbitIn (Subgroup.normalizer (F : Set G)) (Subgroup.zpowers c))
    (h9Ω : (omegaA F).ncard = 9) : False := by
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  have hF' : Sec15R G F c L := sec15R_of_le h hset hF hFL hΩ hcL
  have hD := hF'.toSec13Data
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := h.toSec13Data.le_normalizer h.mem_A
  have h9 : Nat.card (F ⊓ L : Subgroup G) = 9 :=
    card_inf_eq_nine_of_le_sup hD.le_normalizer hcN hD.card_eq hFL h.toSec13Data.orderOf_eq
      hcL hD.mem_A
  obtain ⟨f, hfF, hfL, hfc⟩ := exists_mem_inf_not_mem_of_card_nine hD.card_zpowers h9
  have htr : ∀ F' ∈ omegaA F, ∃ w ∈ Subgroup.normalizer (F : Set G),
      F' = (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom := by
    intro F' hF'Ω
    rw [hΩ] at hF'Ω
    exact hF'Ω
  have hNH : ¬ Subgroup.normalizer (F : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    intro hle
    have := ncard_omegaA_eq_one_of_le hΩ hle
    omega
  rcases h133 G F c L hD hF'.hypS_or_hypT with h1 | ⟨-, -, h3, -⟩ |
      ⟨hirr, -, -, -, -, -, -, hprod, -⟩ | hPGL | ⟨⟨e12⟩⟩ | ⟨⟨eJ⟩⟩
  · exact hNH h1
  · omega
  ·
    rcases h159 G F c L hF' hirr h9 with h1 | ⟨-, -, hT⟩ | ⟨⟨χ⟩, -⟩
    · exact hNH h1
    · have := hT.1
      omega
    · exact false_of_orbit_quot hD (h1510 G F c L hF') htr hfF hfL hfc
        (hBr G F c L hF' ⟨χ⟩ hprod)
  · exact false_of_card_nine_of_isZ3PGLThreePi hD hcL h9 hPGL
  · exact not_isoLThreePi_of_prod_M12 hD e12 hL3
  · exact not_isoLThreePi_of_prod_J2 hD eJ hL3

theorem normalizer_le_of_prod (h133 : Item133) (hBr : Sec16.Step169TwoBridge)
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L) (h159 : Item159 A c L) (h1510 : Item1510 A)
    {p e : ℕ} [Fact p.Prime] (hL3 : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    (hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L)) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  have hD := h.toSec13Data
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 :=
    card_inf_eq_nine hD (isPerfect_lBar hD) hprod.some
  obtain ⟨f, hfA, hfL, hfc⟩ := exists_mem_inf_not_mem_of_card_nine hD.card_zpowers h9
  rcases h133 G A c L hD h.hypS_or_hypT with h1 | ⟨-, ⟨e7⟩, -⟩ |
      ⟨hirr, -, -, -, -, hΩ, -, -, -⟩ | hPGL | ⟨⟨e12⟩⟩ | ⟨⟨eJ⟩⟩
  · exact h1
  · exact (not_isoLThreePi_of_prod_A7 hD e7 hL3).elim
  · rcases h159 hirr h9 with h1 | ⟨⟨ψ⟩, -⟩ | ⟨⟨χ⟩, -⟩
    · exact h1
    · exact (not_isoLThreePi_of_A7 ψ hL3).elim
    · exact (false_of_orbit_quot hD h1510
        (fun F hF => by rw [hΩ] at hF; exact hF) hfA hfL hfc (hBr G A c L h ⟨χ⟩ hprod)).elim
  · exact (Proof1514.false_of_prod_of_isZ3PGLThreePi hD hcL hprod hPGL).elim
  · exact (not_isoLThreePi_of_prod_M12 hD e12 hL3).elim
  · exact (not_isoLThreePi_of_prod_J2 hD eJ hL3).elim

theorem conclusion_of_alt (hset : Item13SetupAt) (h133 : Item133) (h159 : Item159R)
    (h1510 : Sec15.Item1510R) (hBr : Sec16.Step169TwoBridge) (hlist : Step1511List)
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hL3 : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e) {Y : Subgroup G}
    (hY : Y ∈ scriptY0 A (lB A)) (hmeet : MeetsY4 A (lB A) L Y) {P : Subgroup G} (hAP : A ≤ P)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P
      (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)))
    (halt : (Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
        A = omegaOneThree P) ∨
      ∀ F : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 F (Subgroup.zpowers c ⊔ L) →
        F ∈ partTwoF G ∧
          omegaA F = orbitIn (Subgroup.normalizer (F : Set G)) (Subgroup.zpowers c) ∧
          (omegaA F).ncard = 9) :
    Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
      Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y ∧
      ((∃ n f : ℕ, 1 ≤ f ∧ e = n * f ∧ Sec14.IsLThreeEpsAt (↥Y ⧸ CFSG.pCore 2 ↥Y) p f) ∨
        Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))) ∧
      A = omegaOneThree P := by
  rcases halt with ⟨hprod, hΩP⟩ | hFall
  · have hWH := normalizer_le_of_prod h133 hBr h (h159 G A c L h) (h1510 G A c L h) hL3 hprod
    obtain ⟨hYL, htype⟩ := hlist G A c L h p e he hL3 Y hY hmeet P hAP hP hprod hWH hΩP
    exact ⟨hprod, hWH, hYL, htype, hΩP⟩
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨Q⟩ : Nonempty (Sylow 3 ↥(Subgroup.zpowers c ⊔ L)) := inferInstance
    have hFsyl : CFSG.ABGLocalTools.IsSylowOf 3
        ((Q : Subgroup ↥(Subgroup.zpowers c ⊔ L)).map (Subgroup.zpowers c ⊔ L).subtype)
        (Subgroup.zpowers c ⊔ L) := ⟨Q, rfl⟩
    obtain ⟨hF, hΩ, h9⟩ := hFall _ hFsyl
    exact false_of_sylow hset h133 h159 h1510 hBr h hL3 hFsyl.le hF hΩ h9

end Proof1511

theorem rank3II_15_11_of (hset : Item13SetupAt) (h133 : Item133) (h159 : Item159R)
    (h1510 : Sec15.Item1510R) (hBr : Sec16.Step169TwoBridge) (hlist : Step1511List)
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L) (h158 : Item158Y0 A (lB A) c L) :
    Item1511 A (lB A) c L := by
  intro p e _ he hL3 Y hY hmeet P hAP hP
  exact Proof1511.conclusion_of_alt hset h133 h159 h1510 hBr hlist h he hL3 hY hmeet hAP hP
    ((h158 p e he hL3 Y hY hmeet P hAP hP).imp id fun h2 => h2.2.2.2)

end Proof

theorem item1511R_of
    (h158 : Item158Y0R) (hset : Item13SetupAt) (h133 : Item133)
    (h159 : Item159R) (h1510 : Sec15.Item1510R) (hBr : Sec16.Step169TwoBridge)
    (hlist : Step1511List) : Item1511R :=
  fun G _ _ A c L h => rank3II_15_11_of hset h133 h159 h1510 hBr hlist h (h158 G A c L h)

end CFSG.RankThree.PartTwo.Sec15
