module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFStatement
public import CFSG.RankThree.PartTwo.Sec21.Implications
public import CFSG.Adapters.ClassicalCatalogReverse
public import CFSG.Adapters.ExceptionalCatalogReverse
import CFSG.Models.PGLSimple
import CFSG.ClassicalGroups.Symplectic.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G]

theorem ffNotWeaklyClosed_of_not_normalizer_le {A : Subgroup G} {a : G}
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (haA : a ∈ A)
    (hW : ¬ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G)) :
    FFNotWeaklyClosed a := by
  rw [SetLike.not_le_iff_exists] at hW
  obtain ⟨w, hwA, hwa⟩ := hW
  have hzA : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr haA
  refine ⟨w⁻¹, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxA : x ∈ A := hzA hx
    have h1 : w * x * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hwA x).mp hxA
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa [MulAut.conj_apply] using (hAc a haA _ h1).symm
  · intro heq
    apply hwa
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : w * h * w⁻¹ ∈ conjugate (Subgroup.zpowers a) w⁻¹ :=
        ⟨h, hh, by simp [MulAut.conj_apply]⟩
      rwa [heq] at this
    · intro hh
      rw [← heq] at hh
      obtain ⟨y, hy, hyh⟩ := hh
      have : y = h := by simpa [MulAut.conj_apply] using hyh
      exact this ▸ hy

theorem ff_exists_conj_le_sylow {H : Type} [Group H] [Finite H] (P : Sylow 3 H) {K : Subgroup H}
    (hK : IsPGroup 3 K) :
    ∃ g : H, K.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup H) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hK.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q P
  refine ⟨g, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  exact ⟨x, hQ hx, rfl⟩

theorem ff_thetaT_anti {X : Type} [Group X] {p : ℕ} {B B' : Subgroup X} (h : B ≤ B') :
    thetaT p B' ≤ thetaT p B := by
  intro x hx
  simp only [thetaT, Subgroup.mem_iInf] at hx ⊢
  exact fun b hb hb1 => hx b (h hb) hb1

theorem ffSylowHyperplaneOdd_of_mem_partTwoS [Finite G] {A : Subgroup G} (hA : A ∈ partTwoS G)
    {a : G} (haA : a ∈ A) : FFSylowHyperplaneOdd a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro B ⟨P, rfl⟩ B₀ hB₀ hidx
  obtain ⟨⟨hAab, -, E, hE, hEA⟩, -, hT⟩ := hA
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm a haA x hx).symm
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAab.2 g g.2)⟩
  obtain ⟨g, hg⟩ := ff_exists_conj_le_sylow P
    (hAp.comap_subtype (K := Subgroup.centralizer ({a} : Set G)))
  set φ : MulAut G := MulAut.conj (g : G)⁻¹ with hφ
  set Bm : Subgroup G := ((P : Subgroup ↥(Subgroup.centralizer ({a} : Set G))).map
    (Subgroup.centralizer ({a} : Set G)).subtype).map φ.toMonoidHom with hBm
  have hAB : A ≤ Bm := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer ({a} : Set G) := hAC hx
    have h1 : (MulAut.conj g) ⟨x, hxC⟩ ∈ (P : Subgroup ↥(Subgroup.centralizer ({a} : Set G))) :=
      hg ⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    refine ⟨(g : G) * x * (g : G)⁻¹, ⟨_, h1, rfl⟩, ?_⟩
    simp [hφ, MulAut.conj_apply, mul_assoc]
  set B₀' : Subgroup G := B₀.map φ.toMonoidHom with hB₀'
  have hB₀'Bm : B₀' ≤ Bm := Subgroup.map_mono hB₀
  have hidx' : B₀'.relIndex Bm = 3 := by
    rw [hB₀', hBm, Subgroup.relIndex_map_map_of_injective _ _ φ.injective]
    exact hidx
  have hle : B₀'.relIndex A ≤ 3 := by
    have := Subgroup.relIndex_le_of_le_right hAB (show B₀'.relIndex Bm ≠ 0 by rw [hidx']; norm_num)
    rwa [hidx'] at this
  have hcard := Subgroup.relIndex_mul_card B₀' A
  have h27 : 27 ≤ Nat.card A := by
    have := Subgroup.card_dvd_of_le hEA
    rw [hE.2.1] at this
    exact Nat.le_of_dvd Nat.card_pos this
  have h9 : 3 ^ 2 ≤ Nat.card ↥(B₀' ⊓ A) := by
    by_contra hlt
    replace hlt := not_le.mp hlt
    have h8 : Nat.card ↥(B₀' ⊓ A) ≤ 8 := by omega
    have := Nat.mul_le_mul hle h8
    omega
  have hp' : IsPGroup 3 ↥(B₀' ⊓ A) := hAp.to_le inf_le_right
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_three hp' h9
  set B'' : Subgroup G := H.map (B₀' ⊓ A).subtype with hB''
  have hB''card : Nat.card B'' = 9 := by
    rw [hB'', Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hH]
    norm_num
  have hB''le : B'' ≤ B₀' ⊓ A := Subgroup.map_subtype_le H
  have hodd := hT B'' (hB''le.trans inf_le_right) hB''card
  have h1 : thetaT 3 B₀' ≤ thetaT 3 B'' := ff_thetaT_anti (hB''le.trans inf_le_left)
  have h2 : Odd (Nat.card ↥(thetaT 3 B₀')) := hodd.of_dvd_nat (Subgroup.card_dvd_of_le h1)
  have h3 : (thetaT 3 B₀').map φ.symm.toMonoidHom = thetaT 3 B₀ := by
    rw [thetaT_map_equiv Nat.prime_three φ.symm B₀', hB₀', Subgroup.map_map]
    congr 1
    convert Subgroup.map_id B₀
    ext x
    simp
  rw [← h3, Subgroup.card_map_of_injective φ.symm.injective]
  exact h2

theorem ffSylowCommutatorOdd_of_isSylow [Finite G] {A : Subgroup G} (hA : A ∈ partTwoS G) {a : G}
    (hSyl : ∃ P : Sylow 3 ↥(Subgroup.centralizer ({a} : Set G)),
      (P : Subgroup ↥(Subgroup.centralizer ({a} : Set G))).map
        (Subgroup.centralizer ({a} : Set G)).subtype = A) :
    FFSylowCommutatorOdd a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hPA⟩ := hSyl
  rintro B ⟨P', rfl⟩ x hxB hx1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(Subgroup.centralizer ({a} : Set G)) P P'
  have hmem : ∀ z, z ∈ (P' : Subgroup ↥(Subgroup.centralizer ({a} : Set G))) →
      ∃ s ∈ (P : Subgroup ↥(Subgroup.centralizer ({a} : Set G))), g * s * g⁻¹ = z := by
    intro z hz
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    exact ⟨s, hs, rfl⟩
  set φ : MulAut G := MulAut.conj (g : G) with hφ
  have hBA : ((P' : Subgroup ↥(Subgroup.centralizer ({a} : Set G))).map
      (Subgroup.centralizer ({a} : Set G)).subtype) ≤ A.map φ.toMonoidHom := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨s, hs, rfl⟩ := hmem z hz
    refine ⟨(s : G), ?_, by simp [hφ, MulAut.conj_apply]⟩
    rw [← hPA]
    exact ⟨s, hs, rfl⟩
  obtain ⟨y, hyA, hyx⟩ := hBA hxB
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hx1 (by simpa using hyx.symm)
  have hodd := hA.2.1 y hyA hy1
  have hxy : x = φ y := hyx.symm
  have hle : ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({x} : Set G)),
      (P' : Subgroup ↥(Subgroup.centralizer ({a} : Set G))).map
        (Subgroup.centralizer ({a} : Set G)).subtype⁆ ≤
      (⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({y} : Set G)), A⁆).map
        φ.toMonoidHom := by
    rw [Subgroup.map_commutator, map_inSubgroup_aschbacherSolvableCore, map_centralizer_singleton,
      ← hxy]
    exact Subgroup.commutator_mono le_rfl hBA
  rw [← Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective] at hodd
  exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le hle)

theorem ff_isSimpleGroup_lBar {X : Subgroup G} (h : IsL4L5Sp6 X) : IsSimpleGroup (lBar X) := by
  rcases h with ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ | ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ |
    ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩
  · haveI := CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K (d := 4) (by norm_num)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact e.isSimpleGroup
  · haveI := CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K (d := 5) (by norm_num)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact e.isSimpleGroup
  · haveI := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 3 (by norm_num)
      (Or.inr (Or.inr ⟨by simpa using hcard, le_rfl⟩))
    exact e.isSimpleGroup

theorem ff_exists_noncomm_of_isQuasisimple {Q : Type} [Group Q] (h : CFSG.IsQuasisimple Q) :
    ∃ p q : Q, p * q ≠ q * p := by
  obtain ⟨-, -, a, b, hab⟩ := h
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨p, q, fun hpq => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hpq])⟩

theorem ff_aschbacherSolvableCore_eq_center {X : Subgroup G} (hq : CFSG.IsQuasisimple X)
    (hX : IsL4L5Sp6 X) (hQ : CFSG.IsQuasisimple (lBar X)) :
    aschbacherSolvableCore 3 ↥X = Subgroup.center ↥X := by
  haveI := ff_isSimpleGroup_lBar hX
  haveI : IsSimpleGroup (↥X ⧸ Subgroup.center ↥X) := hq.2.1
  obtain ⟨p₀, q₀, hpq₀⟩ := ff_exists_noncomm_of_isQuasisimple hQ
  apply le_antisymm
  ·
    have hN : ((aschbacherSolvableCore 3 ↥X).map (QuotientGroup.mk' (Subgroup.center ↥X))).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((aschbacherSolvableCore 3 ↥X).map (QuotientGroup.mk' (Subgroup.center ↥X))) with h | h
    · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      exact h
    · exfalso
      have hcomm : ∀ p : lBar X, ∃ z ∈ Subgroup.center ↥X, (z : lBar X) = p := by
        intro p
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
        have hx : QuotientGroup.mk' (Subgroup.center ↥X) x ∈
            (aschbacherSolvableCore 3 ↥X).map (QuotientGroup.mk' (Subgroup.center ↥X)) := by
          rw [h]; exact Subgroup.mem_top _
        obtain ⟨n, hn, hnx⟩ := hx
        have hz : n⁻¹ * x ∈ Subgroup.center ↥X := by
          rw [← QuotientGroup.ker_mk' (Subgroup.center ↥X), MonoidHom.mem_ker, map_mul, map_inv,
            hnx, inv_mul_cancel]
        refine ⟨n⁻¹ * x, hz, ?_⟩
        have hn1 : (n : lBar X) = 1 := (QuotientGroup.eq_one_iff n).mpr hn
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hn1, inv_one, one_mul]
      obtain ⟨z₀, hz₀, rfl⟩ := hcomm p₀
      obtain ⟨z₁, hz₁, rfl⟩ := hcomm q₀
      apply hpq₀
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg _ (Subgroup.mem_center_iff.mp hz₁ z₀)
  ·
    have hN : ((Subgroup.center ↥X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((Subgroup.center ↥X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))) with h | h
    · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      exact h
    · exfalso
      have hcomm : ∀ p : lBar X, ∃ z ∈ Subgroup.center ↥X, (z : lBar X) = p := by
        intro p
        have hp : p ∈ (Subgroup.center ↥X).map
            (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) := by
          rw [h]; exact Subgroup.mem_top _
        obtain ⟨z, hz, hzp⟩ := hp
        exact ⟨z, hz, hzp⟩
      obtain ⟨z₀, hz₀, rfl⟩ := hcomm p₀
      obtain ⟨z₁, hz₁, rfl⟩ := hcomm q₀
      apply hpq₀
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg _ (Subgroup.mem_center_iff.mp hz₁ z₀)

theorem ff_statedModel_center {X : Subgroup G} (hq : CFSG.IsQuasisimple X) (hX : IsL4L5Sp6 X)
    (hQ : CFSG.IsQuasisimple (lBar X)) :
    StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 4 2 1 ∨
      StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 5 2 1 ∨
      StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSp 3 2 1 := by
  have eZ : lBar X ≃* (↥X ⧸ Subgroup.center ↥X) :=
    QuotientGroup.quotientMulEquivOfEq (ff_aschbacherSolvableCore_eq_center hq hX hQ)
  rcases hX with h | h | h
  · exact Or.inl (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eZ h)
  · exact Or.inr (Or.inl (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eZ h))
  · exact Or.inr (Or.inr (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eZ h))

theorem ff_not_three_dvd_card_center [Finite G] {X : Subgroup G} (hq : CFSG.IsQuasisimple X)
    (hX : IsL4L5Sp6 X) (hQ : CFSG.IsQuasisimple (lBar X)) :
    ¬ 3 ∣ Nat.card (Subgroup.center ↥X) := by
  have := (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.2.1
  rwa [ff_aschbacherSolvableCore_eq_center hq hX hQ] at this

structure Sec21Point (G : Type) [Group G] [Finite G] (A : Subgroup G) (a : G) (X : Subgroup G) :
    Prop extends Sec21Std G A where
  mem : a ∈ A
  ne_one : a ≠ 1
  mem_lStar : X ∈ lStar A
  mem_theta : X ∈ thetaComponentsAt 3 a

theorem Sec21Pair.toPoint [Finite G] {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec21Pair G A E U c L) : Sec21Point G A c L := by
  have hp := mem_lThreeStarPairs_iff.mp h.mem_pair
  exact { h.toSec21Std with
    mem := h.mem_E.2 hp.1.1
    ne_one := hp.2.1
    mem_lStar := lZeroStar_subset_lStar A (lZeroStarAt_subset_lZeroStar A c hp.2.2.1)
    mem_theta := lZeroStarAt_subset A c hp.2.2.1 }

section Certified

theorem inCatalog_of_ff_outcome {G : Type} [Group G]
    (h : StatedClassicalModel G .PSL 6 2 1 ∨ StatedClassicalModel G .POmegaMinus 4 2 1 ∨
      StatedClassicalModel G .PSL 7 2 1 ∨ StatedClassicalModel G .PSp 4 2 1 ∨
      CFSG.Blueprint.ChevalleyExceptionalModel G .F4 2 1) : CFSG.Assembly.InCatalog G := by
  rcases h with h | h | h | h | h
  · exact CFSG.ClassicalModels.inCatalog_of_statedClassicalModel G _ _ _ _ h
  · exact CFSG.ClassicalModels.inCatalog_of_statedClassicalModel G _ _ _ _ h
  · exact CFSG.ClassicalModels.inCatalog_of_statedClassicalModel G _ _ _ _ h
  · exact CFSG.ClassicalModels.inCatalog_of_statedClassicalModel G _ _ _ _ h
  · exact CFSG.TauCetiBridge.chevalleyExceptionalModel_inCatalog
      (by simp [CFSG.Blueprint.chevalleyExceptionalTags]) h

end Certified

end CFSG.RankThree.PartTwo.Sec21
