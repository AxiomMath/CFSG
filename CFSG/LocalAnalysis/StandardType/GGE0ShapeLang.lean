module

public import CFSG.LocalAnalysis.StandardType.GGLangFamily
public import CFSG.LocalAnalysis.StandardType.GGTwE6LangRetype
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Core
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagramRealized
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE

private theorem exists_langDatum_of_fix_pow_three
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {f : ℕ} (hf : 1 ≤ f) (D : LangDatum .E6 L) (hDq : D.q = 2 ^ f)
    (y : ModGL .E6 L) (hy : y ∈ D.fix) (hy3 : y ^ 3 = 1) :
    ∃ D' : LangDatum .E6 L, D'.Φ = D.Φ ∧ D'.q = D.q ∧
      y ∈ D'.torus.map (MulAut.conj D'.g0).toMonoidHom := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyG : y ∈ adjointGroup .E6 L := ((LangDatum.mem_fix (D := D)).1 hy).1
  have hyΦ : D.Φ y = y := ((LangDatum.mem_fix (D := D)).1 hy).2
  have hconj : ∃ g ∈ adjointGroup .E6 L, g⁻¹ * y * g ∈ torusGroup .E6 L :=
    exists_conj_torusGroup_of_pow_eq_one (τ := .E6) (p := 3) Nat.prime_three
      monomialToralAt_E6_three (ℓ := 2) (by decide) halg hyG hy3
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := D.steinberg
  have hFrEq : Fr = iterateFrobenius L 2 f := by
    refine RingHom.ext fun c => ?_
    rw [hFr, hDq, iterateFrobenius_def]
  have hcop : Nat.Coprime 3 (2 ^ f) := (by decide : Nat.Coprime 3 2).pow_right f
  rcases hP with hP1 | ⟨t, ht, hPt⟩
  · subst hP1
    have hΦ' : D.Φ = entrywiseFrobGL .E6 L 2 f := by
      ext g
      rw [hΦ]
      simp only [one_mul, inv_one, mul_one]
      rw [hFrEq]
    have hfixy : entrywiseFrobGL .E6 L 2 f y = y := by
      rw [← hΦ']
      exact hyΦ
    obtain ⟨D', hD'Φ, hD'q, hD'tor⟩ :=
      exists_langDatum_of_toral_untw (τ := .E6) (ℓ := 2) f hf (p := 3) hcop
        hy3 hfixy hconj
    exact ⟨D', by rw [hD'Φ, hΦ'], by rw [hD'q, hDq], hD'tor⟩
  · cases t with
    | E6 =>
      cases ht
      have hΦt : D.Φ = twistHom TwistTag.E6 L Fr := by
        ext g
        rw [hΦ, hPt]
        rfl
      have hfixy : twistHom TwistTag.E6 L (iterateFrobenius L 2 f) y = y := by
        rw [← hFrEq, ← hΦt]
        exact hyΦ
      obtain ⟨D', hD'Φ, hD'q, hD'tor⟩ :=
        exists_langDatum_of_toral_twisted TwistTag.E6 (ℓ := 2) f hf hfixy hconj
      exact ⟨D', by rw [hD'Φ, hΦt, hFrEq], by rw [hD'q, hDq], hD'tor⟩
    | D4 => exact absurd ht (by decide)

theorem lang_setup_centered_at
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    (S : LangSetup .E6 L 5) (β : ModGL .E6 L)
    (hβ : β ∈ S.D.model) (h3 : β ^ 3 = 1) :
    ∃ (S' : LangSetup .E6 L 5) (g : ModGL .E6 L) (b : Fin Tag.E6.rank → Lˣ),
      g ∈ adjointGroup .E6 L ∧ S'.D.q = S.D.q ∧
      S.D.model.map (MulAut.conj g).toMonoidHom = S'.D.model ∧
      S.Γ.map (MulAut.conj g).toMonoidHom = S'.Γ ∧
      g * β * g⁻¹ = rootDiagUnit .E6 b ∧ rootDiagUnit .E6 b ∈ S'.D.torus ∧
      (∀ j, b j ^ 3 = 1) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p, f, hp, hf, hqeq⟩ := (isPrimePow_nat_iff _).mp S.hqpow.1
  have hp2 : p = 2 := by
    have h0 : ((p : ℕ) : L) = 0 := by
      have h := S.hqpow.2
      rw [← hqeq, Nat.cast_pow] at h
      exact (pow_eq_zero_iff hf.ne').1 h
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      ((CharP.cast_eq_zero_iff L 2 p).1 h0)).symm
  subst hp2
  have hy_fix : S.D.g0 * β * S.D.g0⁻¹ ∈ S.D.fix := by
    rw [← LangDatum.map_conj_model]
    exact ⟨β, hβ, rfl⟩
  have hy3 : (S.D.g0 * β * S.D.g0⁻¹) ^ 3 = 1 := by
    have h := conj_pow (a := S.D.g0) (b := β) (i := 3)
    rw [h, h3]
    group
  have hDq : S.D.q = 2 ^ f := hqeq.symm
  obtain ⟨D', hD'Φ, hD'q, hD'tor⟩ :=
    exists_langDatum_of_fix_pow_three (L := L) halg hf S.D hDq
      (S.D.g0 * β * S.D.g0⁻¹) hy_fix hy3
  obtain ⟨t, ht_mem, ht_eq⟩ := hD'tor
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (τ := .E6)
    (mem_twistedTorusOf.1 ht_mem).1
  have hb3 : ∀ j, b j ^ 3 = 1 := by
    have ht_eq' : t = D'.g0⁻¹ * (S.D.g0 * β * S.D.g0⁻¹) * D'.g0 := by
      rw [← ht_eq]
      change t = D'.g0⁻¹ * (D'.g0 * t * D'.g0⁻¹) * D'.g0
      group
    have ht3 : t ^ 3 = 1 := by
      rw [ht_eq']
      have h := conj_pow (a := D'.g0⁻¹) (b := S.D.g0 * β * S.D.g0⁻¹) (i := 3)
      rw [inv_inv] at h
      rw [h, hy3]
      group
    have h1 : rootDiagUnit .E6 (b ^ 3) = rootDiagUnit .E6 1 := by
      have hmap : rootDiagUnit .E6 (b ^ 3) = (rootDiagUnit .E6 b) ^ 3 :=
        (rootDiagUnitHom .E6 L).map_pow b 3
      rw [hmap, ← hb, ht3, rootDiagUnit_one]
    have h2 : b ^ 3 = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
    intro j
    exact congrFun h2 j
  have hfix' : D'.fix = S.D.fix := by
    ext x
    rw [LangDatum.mem_fix, LangDatum.mem_fix, hD'Φ]
  haveI : Finite ↥S.D.model := S.finite
  have hfinS : Finite S.D.fix := by
    rw [← LangDatum.map_conj_model]
    exact Finite.of_surjective
      ((MulAut.conj S.D.g0).toMonoidHom.subgroupMap S.D.model)
      ((MulAut.conj S.D.g0).toMonoidHom.subgroupMap_surjective S.D.model)
  haveI : Finite ↥S.D.fix := hfinS
  have hfin' : Finite D'.model := by
    rw [LangDatum.model_eq_map_fixModel]
    change Finite ↥((D'.fix).map (MulAut.conj D'.g0⁻¹).toMonoidHom)
    rw [hfix']
    exact Finite.of_surjective
      ((MulAut.conj D'.g0⁻¹).toMonoidHom.subgroupMap S.D.fix)
      ((MulAut.conj D'.g0⁻¹).toMonoidHom.subgroupMap_surjective S.D.fix)
  obtain ⟨ρ', hρ'⟩ := frobeniusOnRoots_proved .E6 L D'
  let S' : LangSetup .E6 L 5 :=
    D'.toSetup 5 ρ' hρ' Nat.prime_five (Or.inl le_rfl)
      (by rw [hD'q]; exact S.hqpow) (by rw [hD'q]; exact S.hpq) hfin'
  let g : ModGL .E6 L := D'.g0⁻¹ * S.D.g0
  have hconjfun : (MulAut.conj g).toMonoidHom.comp (MulAut.conj S.D.g0⁻¹).toMonoidHom =
      (MulAut.conj D'.g0⁻¹).toMonoidHom := by
    have h1 : MulAut.conj g * MulAut.conj S.D.g0⁻¹ = MulAut.conj D'.g0⁻¹ := by
      rw [← map_mul]
      congr 1
      dsimp [g]
      group
    rw [← h1]
    rfl
  refine ⟨S', g, b, ?_, ?_, ?_, ?_, ?_, ?_, hb3⟩
  · exact mul_mem (inv_mem D'.g0_mem) S.D.g0_mem
  · change D'.q = S.D.q
    rw [hD'q, hDq]
  · change S.D.model.map (MulAut.conj g).toMonoidHom = D'.model
    have hM : S.D.model = S.D.fix.map (MulAut.conj S.D.g0⁻¹).toMonoidHom :=
      LangDatum.model_eq_map_fixModel S.D
    have hM' : D'.model = S.D.fix.map (MulAut.conj D'.g0⁻¹).toMonoidHom := by
      rw [LangDatum.model_eq_map_fixModel]
      exact congrArg (fun H => H.map (MulAut.conj D'.g0⁻¹).toMonoidHom) hfix'
    rw [hM, hM', Subgroup.map_map, hconjfun]
  · change S.D.Γ.map (MulAut.conj g).toMonoidHom = D'.Γ
    have hG : S.D.Γ = (⁅S.D.fix, S.D.fix⁆).map (MulAut.conj S.D.g0⁻¹).toMonoidHom := by
      rw [← LangDatum.map_conj_Γ S.D, Subgroup.map_map, conj_inv_comp_conj, Subgroup.map_id]
    have hG' : D'.Γ = (⁅S.D.fix, S.D.fix⁆).map (MulAut.conj D'.g0⁻¹).toMonoidHom := by
      rw [← hfix', ← LangDatum.map_conj_Γ D', Subgroup.map_map, conj_inv_comp_conj,
        Subgroup.map_id]
    rw [hG, hG', Subgroup.map_map, hconjfun]
  · have h1 : g * β * g⁻¹ = D'.g0⁻¹ * (S.D.g0 * β * S.D.g0⁻¹) * D'.g0 := by
      dsimp [g]
      group
    rw [h1]
    have h2 : D'.g0⁻¹ * (S.D.g0 * β * S.D.g0⁻¹) * D'.g0 = t := by
      rw [← ht_eq]
      change D'.g0⁻¹ * (D'.g0 * t * D'.g0⁻¹) * D'.g0 = t
      group
    rw [h2, ← hb]
  · change rootDiagUnit .E6 b ∈ D'.torus
    rw [← hb]
    exact ht_mem

end CFSG.StandardType
