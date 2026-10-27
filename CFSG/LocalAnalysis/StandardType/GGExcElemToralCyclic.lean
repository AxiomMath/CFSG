module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcPilotRest
public import CFSG.LocalAnalysis.StandardType.GGExcElemToralFrobeniusFixed
public import CFSG.LocalAnalysis.StandardType.GGExcElemToralLangStep

public section

namespace CFSG.StandardType.ExcElemToral

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality


theorem exists_conj_mem_torusGroup_of_pow_eq_one {τ : Tag} {p : ℕ} [hp : Fact p.Prime]
    (hmon : MonomialToralAt τ p) {K : Type} [Field K] [Finite K] (hpK : ¬ p ∣ Nat.card K)
    {x : ModGL τ (AlgebraicClosure K)} (hx : x ∈ adjointGroup τ (AlgebraicClosure K))
    (hxp : x ^ p = 1) :
    ∃ g ∈ adjointGroup τ (AlgebraicClosure K), g * x * g⁻¹ ∈ torusGroup τ (AlgebraicClosure K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  set ℓ := ringChar K with hℓdef
  set L := AlgebraicClosure K with hLdef
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective _
  have hq : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have hfpos : 1 ≤ (f : ℕ) := f.pos
  have hLchar : ringChar L ≠ p := by
    rw [ringChar.eq L ℓ]
    intro h
    exact hpK (by rw [hq, h]; exact dvd_pow_self p (by omega : (f : ℕ) ≠ 0))
  have hℓp : ℓ ≠ p := by
    rw [← ringChar.eq L ℓ]
    exact hLchar
  have halg := isAlgebraic_zmod_algebraicClosure_of_finite K ℓ
  have hfin : ((Subgroup.zpowers x : Subgroup (ModGL τ L)) : Set (ModGL τ L)).Finite := by
    have : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.out.pos, hxp⟩
    haveI : Finite (Subgroup.zpowers x) := finite_zpowers.2 this
    exact Set.toFinite _
  have hexp : ∀ y ∈ Subgroup.zpowers x, y ^ p = 1 := by
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  obtain ⟨c, hc, hcx⟩ := exists_conj_le_monomial_bar hℓp halg
    (Subgroup.zpowers_le.2 hx) hfin hexp
  obtain ⟨g', hg', hg'x⟩ := exists_conj_mem_torusGroup_of_mem_monomial hmon hLchar
    (hcx x (Subgroup.mem_zpowers x)) (conj_pow_eq_one' c hxp)
  refine ⟨g' * c, mul_mem hg' hc, ?_⟩
  have : g' * c * x * (g' * c)⁻¹ = g' * (c * x * c⁻¹) * g'⁻¹ := by group
  rw [this]
  exact hg'x


theorem ggExcToral_zpowers_of_monomialToral {τ : Tag} {p : ℕ} (hp : p.Prime)
    (hmon : MonomialToralAt τ p)
    (hstab : ∀ (L : Type) [Field L] (a : Fin τ.rank → Lˣ), (∀ i, a i ^ p = 1) →
      rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a)
    {K : Type} [Field K] [Finite K] (hpq : p ∣ Nat.card K - 1)
    (htorus : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    {s : ↥(adjointGroup τ K)} (hs : s ^ p = 1) : GGExcToral τ K (Subgroup.zpowers s) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hpK : ¬ p ∣ Nat.card K := by
    intro h
    have h1 : p ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub h hpq
    have h2 : Nat.card K - (Nat.card K - 1) = 1 := by omega
    rw [h2] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  set ℓ := ringChar K with hℓdef
  set L := AlgebraicClosure K with hLdef
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective _
  have hq : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have hfpos : 1 ≤ (f : ℕ) := f.pos
  set ι : K →+* L := algebraMap K L with hι
  set φ : ModGL τ K →* ModGL τ L := baseChangeGL ι with hφ
  set sL : ModGL τ L := φ (s : ModGL τ K) with hsL
  have hsLG : sL ∈ adjointGroup τ L := CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι s.2
  have hsLp : sL ^ p = 1 := by
    rw [hsL, ← map_pow, ← Subgroup.coe_pow, hs, Subgroup.coe_one, map_one]
  obtain ⟨g, hg, hgt⟩ := exists_conj_mem_torusGroup_of_pow_eq_one hmon hpK hsLG hsLp
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgt
  have hap : ∀ i, a i ^ p = 1 := by
    have h1 : rootDiagUnit τ (a ^ p) = rootDiagUnit τ 1 := by
      have hpow : rootDiagUnit τ (a ^ p) = rootDiagUnit τ a ^ p :=
        (rootDiagUnitHom τ L).map_pow a p
      rw [hpow, ← ha, CFSG.LieType.Chevalley.rootDiagUnit_one]
      calc (g * sL * g⁻¹) ^ p = g * sL ^ p * g⁻¹ := conj_pow
        _ = 1 := by rw [hsLp]; group
    have h2 : a ^ p = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
    exact fun i => congrFun h2 i
  have haq : ∀ i, a i ^ ℓ ^ (f : ℕ) = a i := by
    intro i
    obtain ⟨m, hm⟩ := hpq
    have hq' : ℓ ^ (f : ℕ) = p * m + 1 := by rw [← hq]; omega
    rw [hq', pow_succ, pow_mul, hap i, one_pow, one_mul]
  have hFix : entrywiseFrobGL τ L ℓ (f : ℕ) sL = sL := by
    have hcomp : (iterateFrobenius L ℓ (f : ℕ)).comp ι = ι := by
      refine RingHom.ext fun c => ?_
      change (iterateFrobenius L ℓ f) (ι c) = ι c
      rw [iterateFrobenius_def, ← map_pow]
      congr 1
      rw [← hf]
      exact FiniteField.pow_card c
    rw [hsL, entrywiseFrobGL, CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have hx : entrywiseFrobGL τ L ℓ (f : ℕ) (g⁻¹ * rootDiagUnit τ a * g) =
      g⁻¹ * rootDiagUnit τ a * g := by
    have h0 : g⁻¹ * rootDiagUnit τ a * g = sL := by rw [← ha]; group
    rw [h0]
    exact hFix
  obtain ⟨h, hh, hFh, hhx⟩ := exists_frobenius_fixed_conj_of_toral ℓ hfpos haq (hstab L a hap) hg hx
  obtain ⟨D, hD, j, hj, hhj⟩ := exists_mem_torusGroup_mul_baseChangeGL_of_frobenius_fixed
    (iterateFrobenius L ℓ (f : ℕ)) (fun c => by rw [iterateFrobenius_def, hq]) hh hFh
  have hDa : rootDiagUnit τ a * D = D * rootDiagUnit τ a :=
    rootDiagUnit_mul_comm_of_mem_torusGroup a hD
  have h0 : g⁻¹ * rootDiagUnit τ a * g = sL := by rw [← ha]; group
  have h5 : φ j * sL * (φ j)⁻¹ = rootDiagUnit τ a := by
    have h6 : sL = (φ j)⁻¹ * rootDiagUnit τ a * φ j := by
      rw [← h0, ← hhx, hhj]
      have : (D * φ j)⁻¹ * rootDiagUnit τ a * (D * φ j) =
          (φ j)⁻¹ * (D⁻¹ * rootDiagUnit τ a * D) * φ j := by group
      rw [this]
      have : D⁻¹ * rootDiagUnit τ a * D = rootDiagUnit τ a := by
        rw [mul_assoc, hDa]
        group
      rw [this]
    rw [h6]
    group
  have hrange : ∀ i, ∃ b : Kˣ, Units.map ι.toMonoidHom b = a i := by
    intro i
    have hai : ((a i : Lˣ) : L) ^ Nat.card K = (a i : L) := by
      rw [← Units.val_pow_eq_pow_val, hq, haq i]
    obtain ⟨b, hb⟩ := CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := K) (L := L)
      hai
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [map_zero] at hb
      exact (a i).ne_zero hb.symm
    exact ⟨Units.mk0 b hb0, Units.ext hb⟩
  choose a' ha' using hrange
  have hda' : φ (rootDiagUnit τ a') = rootDiagUnit τ a := by
    rw [hφ, CFSG.LieType.Chevalley.baseChangeGL_rootDiagUnit]
    congr 1
    funext i
    exact ha' i
  have hap' : ∀ i, a' i ^ p = 1 := by
    intro i
    apply Units.map_injective (f := ι.toMonoidHom) ι.injective
    rw [map_pow, ha' i, hap i, map_one]
  have hyeq : j * (s : ModGL τ K) * j⁻¹ = rootDiagUnit τ a' := by
    apply CFSG.LieType.Chevalley.baseChangeGL_injective ι
    rw [map_mul, map_mul, map_inv]
    exact h5.trans hda'.symm
  have hy : j * (s : ModGL τ K) * j⁻¹ ∈ torusGroup τ K := by
    rw [hyeq]
    exact htorus a' hap'
  refine ⟨⟨j, hj⟩, fun x hx => ?_⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have : (((⟨j, hj⟩ : ↥(adjointGroup τ K)) * s ^ n * (⟨j, hj⟩ : ↥(adjointGroup τ K))⁻¹ :
      ↥(adjointGroup τ K)) : ModGL τ K) = (j * (s : ModGL τ K) * j⁻¹) ^ n := by
    rw [← conj_zpow]
    simp
  rw [this]
  exact Subgroup.zpow_mem _ hy n

end CFSG.StandardType.ExcElemToral
