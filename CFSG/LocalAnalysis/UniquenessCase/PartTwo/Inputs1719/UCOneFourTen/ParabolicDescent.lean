module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.RadicalSz
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreRadicalNormalizer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreFacts
import CFSG.GroupTheory.PCoreOfCentralQuotient
import CFSG.GroupTheory.PCoreSurjective
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fitting
import CFSG.LieType.Simplicity.Suzuki
import CFSG.Blueprint.LieModelAPI
public import CFSG.LieType.BorelTits.CentralQuotient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreSlices

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private lemma normalizer_subgroupOf_map_eq {X : Type} [Group X] {K U : Subgroup X} (hUK : U ≤ K) :
    (normalizer ((U.subgroupOf K : Subgroup ↥K) : Set ↥K)).map K.subtype =
      K ⊓ normalizer (U : Set X) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hUK, Subgroup.subgroupOf_map_subtype, inf_comm]

theorem card_normalizer_subgroupOf {X : Type} [Group X] {K U : Subgroup X} (hUK : U ≤ K) :
    Nat.card ↥(normalizer ((U.subgroupOf K : Subgroup ↥K) : Set ↥K)) =
      Nat.card ↥(K ⊓ normalizer (U : Set X)) := by
  rw [← normalizer_subgroupOf_map_eq hUK,
    Subgroup.card_map_of_injective (f := K.subtype) K.subtype_injective]

private lemma exists_isSz_map_of_central_ker {A A' : Type} [Group A] [Group A']
    (f : A →* A') (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 1 → a ∈ Subgroup.center A)
    {B : Subgroup A} (hBc : CFSG.Open.IsComponentOf B ⊤) {n : ℕ} (hBsz : IsSz ↥B n) :
    ∃ B' : Subgroup A', CFSG.Open.IsComponentOf B' ⊤ ∧ IsSz ↥B' n := by
  have hcomp : CFSG.Open.IsComponentOf (B.map f) ⊤ := by
    have h := CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map f hker hBc
    rwa [Subgroup.map_top_of_surjective f hf] at h
  refine ⟨B.map f, hcomp, ?_⟩
  have hSuz : CFSG.Blueprint.SuzukiModel ↥B 2 n :=
    (CFSG.Blueprint.LieModel.suzukiModel hBsz).2
  have hsimple : IsSimpleGroup ↥B :=
    (CFSG.LieType.Simplicity.fam_2b2_simplicity ↥B 2 n hSuz).2
  have := hsimple
  have hcenter : Subgroup.center ↥B = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥B) with h | h
    · exact h
    · exfalso
      have hcomm : IsMulCommutative ↥B := Subgroup.center_eq_top_iff.mp h
      have := hcomm
      have hca : _root_.commutator ↥B = ⊥ := commutator_eq_bot ↥B
      rw [hBc.2.2.1] at hca
      exact top_ne_bot hca
  let φ : ↥B →* A' := f.comp B.subtype
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hc : (x : A) ∈ Subgroup.center A := hker (x : A) hx
    have hcx : x ∈ Subgroup.center ↥B := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      simpa using (Subgroup.mem_center_iff.mp hc (y : A))
    rw [hcenter] at hcx
    exact Subgroup.mem_bot.mp hcx
  have hrange : φ.range = B.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact CFSG.Blueprint.LieModel.of_mulEquiv
    ((MonoidHom.ofInjective hφinj).trans (MulEquiv.subgroupCongr hrange)) hBsz

theorem exists_radicalSz_quotient_center {K : Type} [Group K] [Finite K]
    (hodd : Odd (Nat.card (center K))) {U : Subgroup K} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hrad : CFSG.Open.pCoreOf 2 (normalizer (U : Set K)) = U) {n : ℕ}
    (hB : ∃ B : Subgroup (↥(normalizer (U : Set K)) ⧸ CFSG.pCore 2 ↥(normalizer (U : Set K))),
      CFSG.Open.IsComponentOf B ⊤ ∧ IsSz ↥B n) :
    ∃ V : Subgroup (K ⧸ center K), V ≠ ⊥ ∧ IsPGroup 2 V ∧
      CFSG.Open.pCoreOf 2 (normalizer (V : Set (K ⧸ center K))) = V ∧
      ∃ B : Subgroup (↥(normalizer (V : Set (K ⧸ center K))) ⧸
          CFSG.pCore 2 ↥(normalizer (V : Set (K ⧸ center K)))),
        CFSG.Open.IsComponentOf B ⊤ ∧ IsSz ↥B n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup K := Subgroup.center K with hZdef
  have hZle : Z ≤ Subgroup.center K := le_of_eq hZdef
  have hZcop : Nat.Coprime (Nat.card Z) 2 := by
    rw [hZdef]
    exact hodd.coprime_two_right
  have hUZ : U ⊓ Z = ⊥ := by
    apply Subgroup.inf_eq_bot_of_coprime
    obtain ⟨k, hk⟩ := hU2.exists_card_eq
    rw [hk]
    exact hZcop.symm.pow_left k
  have hV1 : U.map (QuotientGroup.mk' Z) ≠ ⊥ := by
    intro hbot
    have hle : U ≤ Z := by
      rw [← QuotientGroup.ker_mk' Z]
      exact (Subgroup.map_eq_bot_iff U).mp hbot
    exact hU (le_bot_iff.mp (hUZ ▸ le_inf le_rfl hle))
  have hV2 : IsPGroup 2 (U.map (QuotientGroup.mk' Z)) := hU2.map (QuotientGroup.mk' Z)
  have hNcomap : normalizer (U : Set K) =
      (normalizer (U.map (QuotientGroup.mk' Z) : Set (K ⧸ Z))).comap (QuotientGroup.mk' Z) :=
    CFSG.LieType.BorelTits.normalizer_eq_comap_normalizer_map Z hZle hZcop hU2
  have hN : normalizer (U.map (QuotientGroup.mk' Z) : Set (K ⧸ Z)) =
      (normalizer (U : Set K)).map (QuotientGroup.mk' Z) := by
    have h := Subgroup.map_comap_eq_self_of_surjective (f := QuotientGroup.mk' Z)
      (QuotientGroup.mk'_surjective Z) (normalizer (U.map (QuotientGroup.mk' Z) : Set (K ⧸ Z)))
    rw [← h, ← hNcomap]
  have hZM : Z ≤ normalizer (U : Set K) :=
    hZle.trans (Subgroup.center_le_normalizer (U : Set K))
  have hVrad : CFSG.Open.pCoreOf 2
      (normalizer (U.map (QuotientGroup.mk' Z) : Set (K ⧸ Z))) = U.map (QuotientGroup.mk' Z) := by
    have h1 : CFSG.Open.pCoreOf 2 ((normalizer (U : Set K)).map (QuotientGroup.mk' Z)) =
        (CFSG.Open.pCoreOf 2 (normalizer (U : Set K))).map (QuotientGroup.mk' Z) :=
      CFSG.GroupTheory.pCoreOf_map_mk'_eq_of_le hZle hZcop hZM
    rw [hN, h1, hrad]
  obtain ⟨B, hBc, hBsz⟩ := hB
  set M : Subgroup K := normalizer (U : Set K) with hMdef
  set V : Subgroup (K ⧸ Z) := U.map (QuotientGroup.mk' Z) with hVdef
  set N : Subgroup (K ⧸ Z) := normalizer (V : Set (K ⧸ Z)) with hNdef
  have hNM : N = M.map (QuotientGroup.mk' Z) := hN
  let ρ : ↥M →* ↥N := MonoidHom.codRestrict ((QuotientGroup.mk' Z).comp M.subtype) N (fun x => by
    rw [hNM]
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' Z) x.2)
  have hρval : ∀ x : ↥M, ((ρ x : ↥N) : K ⧸ Z) = (QuotientGroup.mk' Z) (x : K) := fun _ => rfl
  have hρsurj : Function.Surjective ρ := by
    intro y
    have hy : (y : K ⧸ Z) ∈ M.map (QuotientGroup.mk' Z) := by
      rw [← hNM]; exact y.2
    obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨m, hm⟩, Subtype.ext hmy⟩
  have hρcore : CFSG.pCore 2 ↥M ≤ (CFSG.pCore 2 ↥N).comap ρ := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hxU : (x : K) ∈ U := by
      have h := Subgroup.mem_map_of_mem M.subtype hx
      rwa [show (CFSG.pCore 2 ↥M).map M.subtype = U from hrad] at h
    have hmemV : (QuotientGroup.mk' Z) (x : K) ∈ V :=
      Subgroup.mem_map_of_mem (QuotientGroup.mk' Z) hxU
    have h2 : ((ρ x : ↥N) : K ⧸ Z) ∈ V := by
      rw [hρval x]
      exact hmemV
    have h1 : ((ρ x : ↥N) : K ⧸ Z) ∈ CFSG.Open.pCoreOf 2 N := by
      rw [show CFSG.Open.pCoreOf 2 N = V from hVrad]
      exact h2
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp h1
    have hyx : y = ρ x := Subtype.ext hxy
    exact hyx ▸ hy
  let f : (↥M ⧸ CFSG.pCore 2 ↥M) →* (↥N ⧸ CFSG.pCore 2 ↥N) :=
    QuotientGroup.map (CFSG.pCore 2 ↥M) (CFSG.pCore 2 ↥N) ρ hρcore
  have hfsurj : Function.Surjective f :=
    QuotientGroup.map_surjective_of_surjective (CFSG.pCore 2 ↥M) (CFSG.pCore 2 ↥N) ρ
      (fun y => by
        obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
        obtain ⟨x, rfl⟩ := hρsurj z
        exact ⟨x, rfl⟩) hρcore
  have hfker : ∀ y : ↥M ⧸ CFSG.pCore 2 ↥M, f y = 1 →
      y ∈ Subgroup.center (↥M ⧸ CFSG.pCore 2 ↥M) := by
    intro y hy
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) y
    have hy1 : ρ m ∈ CFSG.pCore 2 ↥N := by
      rw [QuotientGroup.map_mk'] at hy
      exact (QuotientGroup.eq_one_iff (ρ m)).mp hy
    have hπm : (QuotientGroup.mk' Z) (m : K) ∈ V := by
      have h2 : ((ρ m : ↥N) : K ⧸ Z) ∈ V := by
        have hh : ((ρ m : ↥N) : K ⧸ Z) ∈ CFSG.Open.pCoreOf 2 N :=
          Subgroup.mem_map_of_mem N.subtype hy1
        rwa [show CFSG.Open.pCoreOf 2 N = V from hVrad] at hh
      rwa [hρval m] at h2
    obtain ⟨u, huU, huπ⟩ := Subgroup.mem_map.mp hπm
    have hzu : (u⁻¹ * (m : K)) ∈ Z := by
      have hker : (u⁻¹ * (m : K)) ∈ (QuotientGroup.mk' Z).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, huπ, inv_mul_cancel]
      rw [QuotientGroup.ker_mk' Z] at hker
      exact hker
    let mu : ↥M := ⟨u, Subgroup.le_normalizer huU⟩
    let mz : ↥M := ⟨u⁻¹ * (m : K), hZM hzu⟩
    have hm : m = mu * mz := by
      apply Subtype.ext
      simp only [mu, mz, Subgroup.coe_mul]
      group
    have hmu : mu ∈ CFSG.pCore 2 ↥M := by
      have h1 : u ∈ CFSG.Open.pCoreOf 2 M := by
        rw [show CFSG.Open.pCoreOf 2 M = U from hrad]
        exact huU
      obtain ⟨u', hu', hu'u⟩ := Subgroup.mem_map.mp h1
      have huu : u' = mu := Subtype.ext hu'u
      exact huu ▸ hu'
    have hmu1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) mu = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hmu
    have hmz : QuotientGroup.mk' (CFSG.pCore 2 ↥M) mz ∈
        Subgroup.center (↥M ⧸ CFSG.pCore 2 ↥M) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) y
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp (hZle hzu) (y' : K)
    have hmeq : QuotientGroup.mk' (CFSG.pCore 2 ↥M) m =
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) mz := by
      rw [hm, map_mul, hmu1, one_mul]
    rw [hmeq]
    exact hmz
  obtain ⟨B', hB'c, hB'sz⟩ :=
    exists_isSz_map_of_central_ker f hfsurj hfker hBc hBsz
  exact ⟨U.map (QuotientGroup.mk' Z), hV1, hV2, hVrad, B', hB'c, hB'sz⟩

namespace CoreSetup

variable {X : Type} [Group X] [Finite X] {K L T Y : Subgroup X} {n : ℕ}

theorem exists_radicalSz_K (h : CoreSetup X K L T Y n) (hL2 : CFSG.Open.pCoreOf 2 L ≠ ⊥) :
    ∃ U : Subgroup ↥K, U ≠ ⊥ ∧ IsPGroup 2 U ∧
      CFSG.Open.pCoreOf 2 (normalizer (U : Set ↥K)) = U ∧
      ∃ B : Subgroup (↥(normalizer (U : Set ↥K)) ⧸ CFSG.pCore 2 ↥(normalizer (U : Set ↥K))),
        CFSG.Open.IsComponentOf B ⊤ ∧ IsSz ↥B n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U₀, hU0, hU0K, -, hrad0, -, -, -, -, -, hcomp, ⟨e₀⟩⟩ :=
    h.exists_radical_normalizer hL2
  have hU02 : IsPGroup 2 U₀ := hrad0 ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  set P : Subgroup X := K ⊓ normalizer (U₀ : Set X) with hPdef
  have hrad0' : CFSG.Open.pCoreOf 2 P = U₀ := hrad0
  set U : Subgroup ↥K := U₀.subgroupOf K with hUdef
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hd : U₀ ⊓ K = ⊥ := by
      have h1 := Subgroup.subgroupOf_eq_bot.mp (hUdef ▸ hbot)
      rwa [disjoint_iff] at h1
    rw [inf_of_le_left hU0K] at hd
    exact hU0 hd
  have hU2 : IsPGroup 2 U := hU02.of_equiv (Subgroup.subgroupOfEquivOfLe hU0K).symm
  set N : Subgroup ↥K := normalizer (U : Set ↥K) with hNdef
  have hNP : N.map K.subtype = P := by
    rw [hNdef, hUdef, hPdef]
    exact normalizer_subgroupOf_map_eq hU0K
  let φ : ↥N ≃* ↥P :=
    (Subgroup.equivMapOfInjective N K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hNP)
  have hφval : ∀ x : ↥N, ((φ x : ↥P) : X) = (x : K) := fun _ => rfl
  have hφ : (CFSG.pCore 2 ↥N).map φ.toMonoidHom = CFSG.pCore 2 ↥P := by
    have hker : IsPGroup 2 (φ.toMonoidHom).ker := by
      rw [(MonoidHom.ker_eq_bot_iff φ.toMonoidHom).mpr φ.injective]
      exact IsPGroup.of_bot
    exact CFSG.map_pCore_eq_of_surjective_of_isPGroup_ker φ.toMonoidHom φ.surjective hker
  have himg : ((CFSG.pCore 2 ↥N).map N.subtype).map K.subtype = U₀ := by
    have hcomp' : K.subtype.comp N.subtype = P.subtype.comp φ.toMonoidHom := by
      ext x
      exact (hφval x).symm
    rw [Subgroup.map_map]
    rw [show K.subtype.comp N.subtype = P.subtype.comp φ.toMonoidHom from hcomp']
    rw [← Subgroup.map_map, hφ]
    exact hrad0'
  have hUrad : CFSG.Open.pCoreOf 2 (normalizer (U : Set ↥K)) = U := by
    apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
    show ((CFSG.pCore 2 ↥N).map N.subtype).map K.subtype = (U₀.subgroupOf K).map K.subtype
    rw [himg, Subgroup.subgroupOf_map_subtype, inf_of_le_left hU0K]
  let ε : ↥N ⧸ CFSG.pCore 2 ↥N ≃* ↥P ⧸ CFSG.pCore 2 ↥P :=
    QuotientGroup.congr (CFSG.pCore 2 ↥N) (CFSG.pCore 2 ↥P) φ hφ
  let Ls : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P) :=
    (L.subgroupOf P).map (QuotientGroup.mk' (CFSG.pCore 2 ↥P))
  have hLsc : CFSG.Open.IsComponentOf Ls ⊤ := hcomp
  let B : Subgroup (↥N ⧸ CFSG.pCore 2 ↥N) := Ls.map (ε.symm : ↥P ⧸ CFSG.pCore 2 ↥P →*
    ↥N ⧸ CFSG.pCore 2 ↥N)
  have hBc : CFSG.Open.IsComponentOf B ⊤ := by
    have htop : (⊤ : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)).map
        (ε.symm : ↥P ⧸ CFSG.pCore 2 ↥P →* ↥N ⧸ CFSG.pCore 2 ↥N) = ⊤ :=
      Subgroup.map_top_of_surjective _ ε.symm.surjective
    rw [← htop]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map ε.symm hLsc
  have hBsz : IsSz ↥B n := by
    have he1 : ↥Ls ≃* ↥B :=
      Subgroup.equivMapOfInjective Ls (ε.symm : ↥P ⧸ CFSG.pCore 2 ↥P →*
        ↥N ⧸ CFSG.pCore 2 ↥N) ε.symm.injective
    exact CFSG.Blueprint.LieModel.of_mulEquiv he1
      (CFSG.Blueprint.LieModel.of_mulEquiv e₀.symm h.sz)
  exact ⟨U, hUne, hU2, hUrad, B, hBc, hBsz⟩

theorem lieModel_twistedF4 (hF3 : RadicalSzComponent) (h : CoreSetup X K L T Y n)
    (hev : CFSG.Blueprint.EvenLieType (↥K ⧸ center ↥K)) (hL2 : CFSG.Open.pCoreOf 2 L ≠ ⊥) :
    CFSG.Blueprint.LieModel (↥K ⧸ center ↥K) .twistedF4 0 2 n := by
  obtain ⟨U, hU1, hU2, hUrad, hB⟩ := h.exists_radicalSz_K hL2
  obtain ⟨V, hV1, hV2, hVrad, hB'⟩ :=
    exists_radicalSz_quotient_center h.odd_card_center hU1 hU2 hUrad hB
  exact hF3 _ V n h.quasisimple.2 hev hV1 hV2 hVrad hB'

end CoreSetup

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
