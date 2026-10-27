module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairCoreGood
import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
import CFSG.LieType.Chevalley.SingleEdgePerfect

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
  CFSG.StandardType.GGFinModel CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


private theorem step_conj_g0 {τ : Tag} (S : LangSetup τ GGL 5) (x : ModGL τ GGL) :
    S.D.step (S.D.g0⁻¹ * x * S.D.g0) = S.D.g0⁻¹ * S.D.Φ x * S.D.g0 := by
  change S.D.n * S.D.Φ (S.D.g0⁻¹ * x * S.D.g0) * S.D.n⁻¹ =
    S.D.g0⁻¹ * S.D.Φ x * S.D.g0
  rw [map_mul, map_mul, map_inv, S.D.lang]
  group

private theorem map_Phi_rootSubgroup {τ : Tag} (S : LangSetup τ GGL 5) {Fr : GGL →+* GGL}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦeq : S.D.Φ = Units.map (entrywiseHom Fr))
    (α : Fin τ.rank → ℤ) :
    (rootSubgroup τ GGL α).map S.D.Φ = rootSubgroup τ GGL α := by
  rw [hΦeq]
  exact map_rootSubgroup_of_eq (g := Fr) (S.frobenius_bijective hFr).2 fun c =>
    Units.ext (entrywise_pinnedX Fr α c)

private theorem langSetup_isAlgebraic_GGL {τ : Tag} (S : LangSetup τ GGL 5) : S.IsAlgebraic := by
  obtain ⟨ℓ, f0, hℓ, hf0, hqf⟩ := S.hqpow.1
  have hℓ2 : ℓ = 2 := by
    have h0 : ((S.D.q : ℕ) : GGL) = 0 := S.hqpow.2
    rw [← hqf, Nat.cast_pow] at h0
    have hz : ((ℓ : ℕ) : GGL) = 0 := (pow_eq_zero_iff hf0.ne').1 h0
    have h2dvd : 2 ∣ ℓ := (CharP.cast_eq_zero_iff GGL 2 ℓ).1 hz
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Nat.prime_iff.mpr hℓ)).1 h2dvd).symm
  subst hℓ2
  intro c
  have hint : IsIntegral (ZMod 2) c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
  have hfd : FiniteDimensional (ZMod 2) (IntermediateField.adjoin (ZMod 2) {c}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hfin : Finite (IntermediateField.adjoin (ZMod 2) {c}) := Module.finite_of_finite (ZMod 2)
  letI : Fintype (IntermediateField.adjoin (ZMod 2) {c}) := Fintype.ofFinite _
  set m := Module.finrank (ZMod 2) (IntermediateField.adjoin (ZMod 2) {c}) with hm
  have hmpos : 0 < m := Module.finrank_pos
  have hcard : Fintype.card (IntermediateField.adjoin (ZMod 2) {c}) = 2 ^ m := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2)
      (V := IntermediateField.adjoin (ZMod 2) {c})
    rw [← hm] at h
    rw [h, ZMod.card]
  have hcm : c ^ (2 ^ m) = c := by
    have h1 := FiniteField.pow_card
      (⟨c, IntermediateField.mem_adjoin_simple_self (ZMod 2) c⟩ :
        IntermediateField.adjoin (ZMod 2) {c})
    rw [hcard] at h1
    have h2 := congrArg (fun x : IntermediateField.adjoin (ZMod 2) {c} => (x : GGL)) h1
    simpa using h2
  have hiter : ∀ k : ℕ, c ^ ((2 ^ m) ^ k) = c := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, hcm]
  refine ⟨m, hmpos, ?_⟩
  rw [show S.D.q = 2 ^ f0 from hqf.symm, ← pow_mul, mul_comm, pow_mul]
  exact hiter f0

private theorem rckPairCoreGood_of_frobenius {τ : Tag} (S : LangSetup τ GGL 5)
    (γ0 : Fin τ.rank → ℤ) (hγ0 : IsRoot τ γ0)
    (hperf : ∀ (K : Type) [Field K] [Finite K], commutator ↥(adjointGroup τ K) = ⊤)
    (hΦ : ∃ Fr : GGL →+* GGL, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr)) :
    RCKPairCoreGood S := by
  classical
  obtain ⟨Fr, hFr, hΦeq⟩ := hΦ
  obtain ⟨K, hKf, hKfin, hKalg, hKcard⟩ := S.exists_fixedField
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : Algebra K GGL := hKalg
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := fun c => by rw [hKcard]; exact hFr c
  have hSAlg : S.IsAlgebraic := langSetup_isAlgebraic_GGL S
  haveI : Algebra.IsAlgebraic K GGL := ⟨fun c => by
    obtain ⟨n, hn, hc⟩ := hSAlg c
    have hq1 : 1 < Nat.card K ^ n := by
      rw [hKcard]
      exact Nat.one_lt_pow hn.ne' S.hqpow.1.one_lt
    refine ⟨Polynomial.X ^ (Nat.card K ^ n) - Polynomial.X, ?_, ?_⟩
    · exact FiniteField.X_pow_card_sub_X_ne_zero K hq1
    · simp only [map_sub, map_pow, Polynomial.aeval_X]
      rw [hKcard, hc, sub_self]⟩
  set H : Subgroup (ModGL τ GGL) :=
    (adjointGroup τ K).map (baseChangeGL (algebraMap K GGL)) with hHdef
  have hHcomm : ⁅H, H⁆ = H := by
    rw [hHdef, ← Subgroup.map_commutator,
      commutator_self_eq_of_commutator_top (hperf K)]
  have hHle : H ≤ S.D.fix := by
    intro u hu
    rw [hHdef] at hu
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hu
    rw [LangDatum.mem_fix]
    refine ⟨baseChangeGL_mem_adjointGroup _ hy, ?_⟩
    rw [hΦeq]
    exact units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFrK y
  have hH_le_comm : H ≤ ⁅S.D.fix, S.D.fix⁆ := by
    rw [← hHcomm]
    exact Subgroup.commutator_mono hHle hHle
  have hstab (α : Fin τ.rank → ℤ) :
      ((rootSubgroup τ GGL α).map (MulAut.conj S.D.g0⁻¹).toMonoidHom).map S.D.step =
        (rootSubgroup τ GGL α).map (MulAut.conj S.D.g0⁻¹).toMonoidHom := by
    have hcomp : S.D.step.comp (MulAut.conj S.D.g0⁻¹).toMonoidHom =
        (MulAut.conj S.D.g0⁻¹).toMonoidHom.comp S.D.Φ := by
      apply MonoidHom.ext
      intro x
      exact step_conj_g0 S x
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, map_Phi_rootSubgroup S hFr hΦeq α]
  refine ⟨γ0, S.D.g0⁻¹, hγ0, (adjointGroup τ GGL).inv_mem S.D.g0_mem,
    hstab γ0, hstab (-γ0), ?_⟩
  intro r hr
  have hx_fix : S.D.g0 * r * S.D.g0⁻¹ ∈ S.D.fix := by
    rw [← LangDatum.map_conj_model]
    exact Subgroup.mem_map_of_mem _ hr
  have hx_mem := (LangDatum.mem_fix (D := S.D)).1 hx_fix
  have hxC : S.D.g0 * r * S.D.g0⁻¹ ∈ adjointGroup τ GGL := hx_mem.1
  have hxF : Units.map (entrywiseHom Fr) (S.D.g0 * r * S.D.g0⁻¹) =
      S.D.g0 * r * S.D.g0⁻¹ := by
    have h := hx_mem.2
    rwa [hΦeq] at h
  obtain ⟨a, u, huH, hx⟩ :=
    exists_rootDiagUnit_mul_of_frobenius_fixed τ Fr hFrK hxC hxF
  have huH' : u ∈ H := by rwa [hHdef]
  have hu_comm : u ∈ ⁅S.D.fix, S.D.fix⁆ := hH_le_comm huH'
  set d : ModGL τ GGL := baseChangeGL (algebraMap K GGL) (rootDiagUnit τ a) with hddef
  have hd_torus : d ∈ torusGroup τ GGL := by
    rw [hddef, baseChangeGL_rootDiagUnit]
    exact rootDiagUnit_mem_torusGroup _
  have hd_fix : d ∈ S.D.fix := by
    rw [LangDatum.mem_fix]
    refine ⟨CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup' hd_torus, ?_⟩
    rw [hΦeq]
    exact units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFrK (rootDiagUnit τ a)
  set t : ModGL τ GGL := S.D.g0⁻¹ * d * S.D.g0 with htdef
  set u1 : ModGL τ GGL := S.D.g0⁻¹ * (d * u * d⁻¹) * S.D.g0 with hu1def
  have hdu : d * u * d⁻¹ ∈ ⁅S.D.fix, S.D.fix⁆ := by
    have h := rckConj_mem_commutator (M := S.D.fix) (Subgroup.inv_mem _ hd_fix) hu_comm
    simpa using h
  have hu1Γ : u1 ∈ S.Γ := by
    change u1 ∈ S.D.Γ
    have hmem' : d * u * d⁻¹ ∈ S.D.Γ.map (MulAut.conj S.D.g0).toMonoidHom := by
      rw [LangDatum.map_conj_Γ]
      exact hdu
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 hmem'
    have hyu : y = u1 := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyeq
      rw [hu1def, ← hyeq]
      group
    rwa [hyu] at hy
  have ht_norm1 : t ∈ Subgroup.normalizer (conjSub S.D.g0⁻¹ (rootSubgroup τ GGL γ0)) := by
    have hd_norm : d ∈ Subgroup.normalizer (rootSubgroup τ GGL γ0 : Set (ModGL τ GGL)) :=
      CFSG.StandardType.RootCentExc.torusGroup_le_normalizer_rootSubgroup hγ0 hd_torus
    rw [htdef]
    exact rckMem_normalizer_of_conjSub_eq (conjSub_conjSub_inv S.D.g0 (rootSubgroup τ GGL γ0))
      hd_norm
  have ht_norm2 : t ∈ Subgroup.normalizer (conjSub S.D.g0⁻¹ (rootSubgroup τ GGL (-γ0))) := by
    have hd_norm : d ∈ Subgroup.normalizer (rootSubgroup τ GGL (-γ0) : Set (ModGL τ GGL)) :=
      CFSG.StandardType.RootCentExc.torusGroup_le_normalizer_rootSubgroup (IsRoot.neg hγ0)
        hd_torus
    rw [htdef]
    exact rckMem_normalizer_of_conjSub_eq (conjSub_conjSub_inv S.D.g0 (rootSubgroup τ GGL (-γ0)))
      hd_norm
  have hr_eq : r = u1 * t := by
    rw [hu1def, htdef]
    calc r = S.D.g0⁻¹ * (S.D.g0 * r * S.D.g0⁻¹) * S.D.g0 := by group
      _ = S.D.g0⁻¹ * (d * u) * S.D.g0 := by rw [hx]
      _ = (S.D.g0⁻¹ * (d * u * d⁻¹) * S.D.g0) * (S.D.g0⁻¹ * d * S.D.g0) := by group
  refine ⟨u1, hu1Γ, ?_, ?_⟩
  · have h : u1⁻¹ * r = t := by rw [hr_eq]; group
    rw [h]
    exact ht_norm1
  · have h : u1⁻¹ * r = t := by rw [hr_eq]; group
    rw [h]
    exact ht_norm2

theorem rckPairCoreGood_untw {τ : Tag} (hτ : τ = Tag.D4 ∨ τ = Tag.E6 ∨ τ = Tag.E7)
    (S : LangSetup τ GGL 5)
    (hΦ : ∃ Fr : GGL →+* GGL, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr)) :
    RCKPairCoreGood S := by
  rcases hτ with rfl | rfl | rfl
  · exact rckPairCoreGood_of_frobenius S (Pi.single ⟨0, by decide⟩ 1) (isRoot_single _ _)
      (fun K _ _ => single_edge_perfect Tag.D4 K (by decide)) hΦ
  · exact rckPairCoreGood_of_frobenius S (Pi.single ⟨0, by decide⟩ 1) (isRoot_single _ _)
      (fun K _ _ => single_edge_perfect Tag.E6 K (by decide)) hΦ
  · exact rckPairCoreGood_of_frobenius S (Pi.single ⟨0, by decide⟩ 1) (isRoot_single _ _)
      (fun K _ _ => single_edge_perfect Tag.E7 K (by decide)) hΦ

end CFSG.StandardType.RCKRP
