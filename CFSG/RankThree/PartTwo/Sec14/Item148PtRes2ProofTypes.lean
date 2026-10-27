module

public import CFSG.RankThree.PartTwo.Sec14.Item148PointProof142
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofUpper
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofLower
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofCore
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step142TypesOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (h : Sec14Std G A c L),
    letI := ker142_normal (LB := lB A) h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A
    ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
        (piCompl 3),
      k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) →
      (IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12)) →
      ∃ (a : G) (ha : a ∈ A), alpha142 A (lB A) c a ha ≠ 1 ∧
        img142 A (lB A) c Q =
          thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊔ thetaCA142 A (lB A) c

@[expose] noncomputable def Step142TypesM22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (h : Sec14Std G A c L),
    letI := ker142_normal (LB := lB A) h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A
    ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
        (piCompl 3),
      k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) →
      (CFSG.Assembly.IsElemAbelian 2 (img142 A (lB A) c Q) ∧
          Nat.card (img142 A (lB A) c Q) = 16) ∧
        ∃ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A),
          Subgroup.closure {alpha142 A (lB A) c a ha, alpha142 A (lB A) c b hb} =
            img142 A (lB A) c A ∧
          img142 A (lB A) c Q =
            thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊔
              thetaC142 A (lB A) c (alpha142 A (lB A) c b hb) ∧
          thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊓
              thetaC142 A (lB A) c (alpha142 A (lB A) c b hb) = ⊥

@[expose] noncomputable def Step142TypesHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (h : Sec14Std G A c L),
    letI := ker142_normal (LB := lB A) h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A
    ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
        (piCompl 3),
      k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      (∃ T : Sylow 2 (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)),
          Nonempty (↥(img142 A (lB A) c Q) ≃*
            ↥(T : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))))) ∧
        ∃ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A) (d : G) (hd : d ∈ A),
          Subgroup.closure {alpha142 A (lB A) c a ha, alpha142 A (lB A) c b hb} =
            img142 A (lB A) c A ∧
          alpha142 A (lB A) c d hd ≠ 1 ∧
          IsThreeCentralIn (img142 A (lB A) c L) (alpha142 A (lB A) c d hd) ∧
          Subgroup.zpowers (alpha142 A (lB A) c a ha) ≠
            Subgroup.zpowers (alpha142 A (lB A) c d hd) ∧
          Subgroup.zpowers (alpha142 A (lB A) c b hb) ≠
            Subgroup.zpowers (alpha142 A (lB A) c d hd) ∧
          img142 A (lB A) c Q =
            thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊔
                thetaC142 A (lB A) c (alpha142 A (lB A) c b hb) ⊔
              (img142 A (lB A) c Q ⊓
                Subgroup.centralizer {alpha142 A (lB A) c d hd})

namespace Item148PtRes2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_sup_zpowers_le {O : Subgroup G} {c : G}
    (hOc : O ≤ Subgroup.centralizer ({c} : Set G)) :
    ⁅O ⊔ Subgroup.zpowers c, O ⊔ Subgroup.zpowers c⁆ ≤ O := by
  have hcc : Subgroup.zpowers c ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hcC : ∀ X : Subgroup G, X ≤ Subgroup.centralizer ({c} : Set G) →
      Subgroup.zpowers c ≤ Subgroup.centralizer (X : Set G) := fun X hX => by
    rw [Subgroup.le_centralizer_iff, centralizer_zpowers148]
    exact hX
  have hcO : Subgroup.zpowers c ≤ Subgroup.normalizer (O : Set G) :=
    (hcC O hOc).trans (Subgroup.centralizer_le_normalizer _)
  exact commutator_sup_le148 (sup_le Subgroup.le_normalizer hcO) hcO (hcC _ (sup_le hOc hcc))

theorem inf_le_theta (hspor : SporadicModels131) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {O : Subgroup G} (hO3 : ¬ 3 ∣ Nat.card O)
    (hLO : L ≤ Subgroup.normalizer (O : Set G))
    (hOc : O ≤ Subgroup.centralizer ({c} : Set G)) :
    (O ⊔ Subgroup.zpowers c).subgroupOf L ≤ aschbacherSolvableCore 3 ↥L := by
  have hD := h.toSec13Data
  have hLc := hD.le_centralizer
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set N := (O ⊔ Subgroup.zpowers c).subgroupOf L with hN
  have hLz : L ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [centralizer_zpowers148]
    exact hLc
  have hLN : L ≤ Subgroup.normalizer ((O ⊔ Subgroup.zpowers c : Subgroup G) : Set G) :=
    Proof142Res.le_normalizer_sup_of hLO hLz
  have hNn : N.Normal := ⟨fun n hn l => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hLN l.2) n).mp hn⟩
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  have hZ := center_eq_bot_of_sec14 hspor h
  have hLp : Group.IsPerfect (↥L ⧸ θ) := hq.1
  have hS : IsSimpleGroup (↥L ⧸ θ) := by
    let e : (↥L ⧸ θ) ⧸ Subgroup.center (↥L ⧸ θ) ≃* ↥L ⧸ θ :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    have : IsSimpleGroup ((↥L ⧸ θ) ⧸ Subgroup.center (↥L ⧸ θ)) := hq.2.1
    exact e.symm.isSimpleGroup
  have hNbn : (N.map (QuotientGroup.mk' θ)).Normal := hNn.map _ (QuotientGroup.mk'_surjective θ)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' θ)) with hb | ht
  · intro n hn
    have h1 : QuotientGroup.mk' θ n ∈ N.map (QuotientGroup.mk' θ) := ⟨n, hn, rfl⟩
    rwa [hb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  · exfalso
    have hNN : ⁅N, N⁆ ≤ O.subgroupOf L := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      have h1 : (x : G) ∈ (⁅N, N⁆).map L.subtype := ⟨x, hx, rfl⟩
      rw [Subgroup.map_commutator] at h1
      have h2 : N.map L.subtype ≤ O ⊔ Subgroup.zpowers c := by
        rintro _ ⟨n, hn, rfl⟩
        exact Subgroup.mem_subgroupOf.mp hn
      exact commutator_sup_zpowers_le hOc (Subgroup.commutator_mono h2 h2 h1)
    have htop : (⊤ : Subgroup (↥L ⧸ θ)) ≤ (O.subgroupOf L).map (QuotientGroup.mk' θ) := by
      rw [← Group.IsPerfect.commutator_eq_top (G := ↥L ⧸ θ), commutator_def, ← ht,
        ← Subgroup.map_commutator]
      exact Subgroup.map_mono hNN
    have h3L : 3 ∣ Nat.card L :=
      three_dvd_card_of_types148 (h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).1
    have h3Lb : 3 ∣ Nat.card (↥L ⧸ θ) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θ] at h3L
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3L with h | h
      · exact h
      · exact absurd h hθ3
    have hle : Nat.card (↥L ⧸ θ) ∣ Nat.card (O.subgroupOf L) := by
      have h1 := Subgroup.card_dvd_of_le htop
      rw [Subgroup.card_top] at h1
      exact h1.trans (Subgroup.card_map_dvd _ _)
    have hOL : ¬ 3 ∣ Nat.card (O.subgroupOf L) := by
      intro h3
      apply hO3
      have h1 : Nat.card (O.subgroupOf L) = Nat.card (O ⊓ L : Subgroup G) := by
        rw [← Subgroup.card_map_of_injective L.subtype_injective, Subgroup.subgroupOf_map_subtype]
      rw [h1] at h3
      exact h3.trans (Subgroup.card_dvd_of_le inf_le_left)
    exact hOL (h3Lb.trans hle)

theorem nonempty_img142_equiv (hspor : SporadicModels131) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L)
    (hK : k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :
    letI := ker142_normal (LB := lB A) h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A
    Nonempty (↥(img142 A (lB A) c L) ≃* ↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
  have := ker142_normal (LB := lB A) h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hcA := hD.mem_A
  have hLc := hD.le_centralizer
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  set K := k142 A (lB A) c with hKdef
  set O := pPrimeCoreOf 3 K with hO
  have hLK : L ≤ K := hK ▸ le_sup_left.trans le_sup_left
  have hRc := le_centralizer_of_mem_invariantPiSubgroups hcA hD.orderOf_eq
    (sup_mem_invariantPiSubgroups hcA hAab)
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [hK, sup_assoc]
    exact sup_le hLc hRc
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_types148 (h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).1
  have hKN : K ≤ Subgroup.normalizer (L : Set G) :=
    hKc.trans (centralizer_le_normalizer_of_three_dvd h h3L)
  have : (aschbacherSolvableCore 3 ↥L).Characteristic :=
    Sec4.aschbacherSolvableCore_characteristic _
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hθO : inSubgroup (aschbacherSolvableCore 3) L ≤ O := by
    refine le_pPrimeCoreOf ((Subgroup.map_subtype_le _).trans hLK)
      (hKN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)) ?_
    rw [inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 K)
  have hLKA : L ≤ kA142 A (lB A) c := hLK.trans le_sup_left
  set f : ↥L →* ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c :=
    (QuotientGroup.mk' (ker142 A (lB A) c)).comp (Subgroup.inclusion hLKA) with hf
  have hrange : f.range = img142 A (lB A) c L := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hker : f.ker = aschbacherSolvableCore 3 ↥L := by
    ext l
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, ker142, Subgroup.mem_subgroupOf]
    change (l : G) ∈ O ⊔ Subgroup.zpowers c ↔ _
    constructor
    · intro hl
      exact inf_le_theta hspor h hO3 (hLK.trans (le_normalizer_pPrimeCoreOf 3 K))
        ((pPrimeCoreOf_le 3 K).trans hKc) (Subgroup.mem_subgroupOf.mpr hl)
    · intro hl
      exact Subgroup.mem_sup_left (hθO ⟨l, hl, rfl⟩)
  exact ⟨(MulEquiv.subgroupCongr hrange).symm.trans
    ((QuotientGroup.quotientKerEquivRange f).symm.trans (QuotientGroup.quotientMulEquivOfEq hker))⟩

theorem not_isoLThreePi_J2 (p e : ℕ) [Fact p.Prime] :
    ¬ Sec4.IsoLThreePi CFSG.Blueprint.NativeSporadic.J2 p e :=
  KFacts.KS14.not_isoLThreePi_of_card KFacts.KS14.card_nativeJ2
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSL_j2)
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSU_j2) p e

end Item148PtRes2

open Item148PtRes2 in
theorem step142TypesS14_of (hspor : SporadicModels131) (h1 : Step142TypesOne)
    (h2 : Step142TypesM22) (h3 : Step142TypesHJ) : Step142TypesS14 := by
  intro G _ _ A c L h Q hQ hK
  obtain ⟨e⟩ := nonempty_img142_equiv hspor h hK
  rcases (h.chosen136.2 c h.toSec13Data.zpowers_mem_omegaA L h.toSec13Data.mem_lA).1 with
    ⟨⟨φ⟩⟩ | hL3 | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact Or.inr (Or.inr ⟨⟨e.trans φ⟩, h3 G A c L h Q hQ hK ⟨φ⟩⟩)
  · exact Or.inl ⟨Or.inl (isLThreePi_of_mulEquiv e hL3), h1 G A c L h Q hQ hK (Or.inl hL3)⟩
  · exact Or.inl ⟨Or.inr (Or.inl ⟨e.trans φ⟩), h1 G A c L h Q hQ hK (Or.inr (Or.inl ⟨φ⟩))⟩
  · exact Or.inr (Or.inl ⟨⟨e.trans φ⟩, h2 G A c L h Q hQ hK ⟨φ⟩⟩)
  · exact Or.inl ⟨Or.inr (Or.inr ⟨e.trans φ⟩), h1 G A c L h Q hQ hK (Or.inr (Or.inr ⟨φ⟩))⟩

end CFSG.RankThree.PartTwo.Sec14
