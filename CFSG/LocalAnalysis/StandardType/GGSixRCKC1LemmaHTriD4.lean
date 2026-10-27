module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHBruhat
public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcRoots
public import CFSG.LieType.Steinberg.TwistedD4.Datum
public import CFSG.LieType.Steinberg.TwistedD4.Perfect
public import CFSG.ClassicalInvolution.ModelFacts.WeylTransitive
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4BridgeLongRoot

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.SeitzReduction
  CFSG.StandardType CFSG.Open CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.Steinberg.TwistedD4
  CFSG.StandardType.RootCentExc CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem

private theorem rckJB8910_highRootData_D4 :
    RootCentExc.HighRootData d4 (highRoot d4) ⟨2, by decide⟩ where
  maxHeight := ⟨isRoot_highRoot d4, fun _ hα => height_le_height_highRoot hα⟩
  coPair := by decide +kernel
  form := ⟨1, by norm_num, RootCentExc.iform_eq_of_sum (by decide +kernel)⟩

private theorem rckJB8910_exists_smul_highRoot_single (j : Fin d4.rank) :
    ∃ v : WeylGroup d4, v • highRoot d4 = Pi.single j 1 := by
  have h2 : (simple d4 (nd 3) * simple d4 (nd 1) * simple d4 (nd 0) *
      simple d4 (nd 2)) • highRoot d4 = Pi.single (nd 2) 1 := by
    simp only [mul_smul, simple_smul]
    decide +kernel
  have h0 : (simple d4 (nd 2) * simple d4 (nd 0)) •
      (Pi.single (nd 2) 1 : Fin d4.rank → ℤ) = Pi.single (nd 0) 1 := by
    simp only [mul_smul, simple_smul]
    decide +kernel
  have h1 : (simple d4 (nd 2) * simple d4 (nd 1)) •
      (Pi.single (nd 2) 1 : Fin d4.rank → ℤ) = Pi.single (nd 1) 1 := by
    simp only [mul_smul, simple_smul]
    decide +kernel
  have h3 : (simple d4 (nd 2) * simple d4 (nd 3)) •
      (Pi.single (nd 2) 1 : Fin d4.rank → ℤ) = Pi.single (nd 3) 1 := by
    simp only [mul_smul, simple_smul]
    decide +kernel
  have hj : ∀ i : Fin d4.rank, i = nd 0 ∨ i = nd 1 ∨ i = nd 2 ∨ i = nd 3 := by decide
  rcases hj j with rfl | rfl | rfl | rfl
  · exact ⟨_, by rw [mul_smul, h2, h0]⟩
  · exact ⟨_, by rw [mul_smul, h2, h1]⟩
  · exact ⟨_, h2⟩
  · exact ⟨_, by rw [mul_smul, h2, h3]⟩

private theorem rckJB8910_exists_smul_highRoot {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β) :
    ∃ w : WeylGroup d4, w • β = highRoot d4 := by
  obtain ⟨w, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hβ
  obtain ⟨v, hv⟩ := rckJB8910_exists_smul_highRoot_single j
  exact ⟨v⁻¹ * w⁻¹, by rw [mul_smul, inv_smul_smul, ← hv, inv_smul_smul]⟩

private theorem rckJB8910_cent_D4_root
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) {x : ModGL d4 K}
    (hx : x ∈ rootSubgroup d4 K α) (hx1 : x ≠ 1) :
    adjointGroup d4 K ⊓ Subgroup.centralizer {x} ≤
      Subgroup.centralizer (rootSubgroup d4 K α : Set (ModGL d4 K)) := by
  obtain ⟨w, hw⟩ := rckJB8910_exists_smul_highRoot hα
  set n : ModGL d4 K := canonicalRep (coxeterSystem d4) K w with hn
  have hnG : n ∈ adjointGroup d4 K :=
    canonicalRep_mem_adjointGroup (coxeterSystem d4) K w
  have hmap : (rootSubgroup d4 K α).map (MulAut.conj n).toMonoidHom =
      rootSubgroup d4 K (highRoot d4) := by
    have h := (canonical_weyl_root_transport d4 K).2.1 w α hα
    rwa [hw] at h
  have hd := rckJB8910_highRootData_D4
  have hx' : n * x * n⁻¹ ∈ rootSubgroup d4 K (highRoot d4) := by
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  have hx'1 : n * x * n⁻¹ ≠ 1 := by
    intro h
    apply hx1
    calc x = n⁻¹ * (n * x * n⁻¹) * n := by group
      _ = n⁻¹ * 1 * n := by rw [h]
      _ = 1 := by group
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  have hkG : k ∈ adjointGroup d4 K := hk.1
  have hkc : k * x = x * k := Subgroup.mem_centralizer_singleton_iff.1 hk.2
  have hnkG : n * k * n⁻¹ ∈ adjointGroup d4 K := mul_mem (mul_mem hnG hkG) (inv_mem hnG)
  have hnk_cent : n * k * n⁻¹ ∈ Subgroup.centralizer {n * x * n⁻¹} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (n * k * n⁻¹) * (n * x * n⁻¹) = n * (k * x) * n⁻¹ := by group
      _ = n * (x * k) * n⁻¹ := by rw [hkc]
      _ = (n * x * n⁻¹) * (n * k * n⁻¹) := by group
  have hmem := rckHB_cent_highRoot d4 K hd hx' hx'1 ⟨hnkG, hnk_cent⟩
  rw [Subgroup.mem_centralizer_iff] at hmem
  intro y hy
  have hy' : n * y * n⁻¹ ∈ rootSubgroup d4 K (highRoot d4) := by
    rw [← hmap]
    exact ⟨y, hy, rfl⟩
  have hcomm := hmem (n * y * n⁻¹) hy'
  have hkey : n * (y * k) * n⁻¹ = n * (k * y) * n⁻¹ := by
    calc n * (y * k) * n⁻¹ = (n * y * n⁻¹) * (n * k * n⁻¹) := by group
      _ = (n * k * n⁻¹) * (n * y * n⁻¹) := hcomm
      _ = n * (k * y) * n⁻¹ := by group
  have := congrArg (fun z => n⁻¹ * z * n) hkey
  simpa using this

private theorem rckJB8910_cent_D4_rootGroup
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) {x : adjointGroup d4 F}
    (hx : x ∈ rootGroup (rootOperatorFamily d4) F α) (hx1 : x ≠ 1) :
    (Subgroup.centralizer {x} : Subgroup (adjointGroup d4 F)) ≤
      Subgroup.centralizer (rootGroup (rootOperatorFamily d4) F α : Set (adjointGroup d4 F)) := by
  have hxmod : (x : ModGL d4 F) ∈ CFSG.Blueprint.Chevalley.rootSubgroup d4 F α := by
    have h := hx
    rw [rootGroup_of_isRoot hα,
      ← (rootOperatorFamily d4).subgroupOf_rootSubgroup_eq F ⟨α, hα⟩] at h
    exact h
  have hx1mod : (x : ModGL d4 F) ≠ 1 := fun h => hx1 (Subtype.ext h)
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hk' : (k : ModGL d4 F) ∈ adjointGroup d4 F ⊓
      (Subgroup.centralizer {(x : ModGL d4 F)} : Subgroup (ModGL d4 F)) := by
    rw [Subgroup.mem_inf]
    refine ⟨k.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← Subgroup.coe_mul, ← Subgroup.coe_mul]
    exact congrArg (fun z : adjointGroup d4 F => (z : ModGL d4 F))
      (Subgroup.mem_centralizer_singleton_iff.1 hk)
  have hmem := rckJB8910_cent_D4_root hα hxmod hx1mod hk'
  rw [Subgroup.mem_centralizer_iff] at hmem
  have hymod : (y : ModGL d4 F) ∈ CFSG.Blueprint.Chevalley.rootSubgroup d4 F α := by
    have h := hy
    rw [rootGroup_of_isRoot hα,
      ← (rootOperatorFamily d4).subgroupOf_rootSubgroup_eq F ⟨α, hα⟩] at h
    exact h
  show y * k = k * y
  exact Subtype.ext (by simpa [Subgroup.coe_mul] using hmem (y : ModGL d4 F) hymod)

theorem charP_two_of_triField {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ}
    (hF : TriField F σ g) : CharP F 2 := by
  haveI : Fintype F := Fintype.ofFinite F
  have h0 : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, hF.2.1, ← pow_mul] at h0
  rw [Nat.cast_pow, Nat.cast_ofNat] at h0
  have hg : g * 3 ≠ 0 := by have := hF.1; omega
  exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (pow_eq_zero_iff hg |>.mp h0)

private theorem rckJB8910_long_orbit
    {F : Type} [Field F] {σ : F →+* F} {g : ℕ}
    (hF : TriField F σ g)
    {β : Fin (Tag.rank .G2) → ℤ} (hβ : GGLongRoot (twistedDatum σ) β) :
    ∃ w : WeylGroup .G2, w • β = Pi.single (ng 0) 1 := by
  obtain ⟨w, γ₀, hγ₀mem, hmax, hβeq⟩ := hβ
  let W : WeylGroup .G2 := w
  let γ : Fin (Tag.rank .G2) → ℤ := γ₀
  have hβeq' : β = W • γ := hβeq
  have hγ : IsRoot .G2 γ := isRoot_of_mem_twistedDatum_roots σ hγ₀mem
  have hmax' : ∀ δ : Fin (Tag.rank .G2) → ℤ, IsRoot .G2 δ → height δ ≤ height γ := by
    intro δ hδ
    have h := hmax δ (by rw [twistedDatum_roots]; exact hδ)
    exact h
  have hγeq : γ = highRoot .G2 :=
    LieKnownR2.TriD4.Bridge.eq_highRoot_G2_of_height_eq hγ
      (le_antisymm (height_le_height_highRoot (τ := .G2) hγ)
        (hmax' _ (isRoot_highRoot .G2)))
  have hv : (simple .G2 (ng 1) * simple .G2 (ng 0)) • highRoot .G2 =
      Pi.single (ng 0) 1 := by
    simp only [mul_smul, simple_smul]
    decide +kernel
  refine ⟨(simple .G2 (ng 1) * simple .G2 (ng 0)) * W⁻¹, ?_⟩
  rw [mul_smul, hβeq', hγeq, inv_smul_smul, hv]

private theorem rckJB8910_cent_conj {M : LieUniversal} {β β' : Fin M.D.rank → ℤ} {g : M.K}
    (hg : (M.D.rootGroup β).map (MulAut.conj g).toMonoidHom = M.D.rootGroup β')
    (hC : RCKLemmaHCent M β) : RCKLemmaHCent M β' := by
  intro x hx hx1 k hk
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hxg : g⁻¹ * x * g ∈ M.D.rootGroup β := by
    have hx' := hx
    rw [← hg] at hx'
    obtain ⟨z, hz, hzx⟩ := hx'
    have hzx' : g * z * g⁻¹ = x := by simpa [MulAut.conj_apply] using hzx
    have hz_eq : z = g⁻¹ * x * g := by rw [← hzx']; group
    rwa [hz_eq] at hz
  have hxg1 : g⁻¹ * x * g ≠ 1 := by
    intro h
    apply hx1
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [h]
      _ = 1 := by group
  have hkg : g⁻¹ * k * g ∈ Subgroup.centralizer {g⁻¹ * x * g} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hkx : k * x = x * k := Subgroup.mem_centralizer_singleton_iff.1 hk
    calc (g⁻¹ * k * g) * (g⁻¹ * x * g) = g⁻¹ * (k * x) * g := by group
      _ = g⁻¹ * (x * k) * g := by rw [hkx]
      _ = (g⁻¹ * x * g) * (g⁻¹ * k * g) := by group
  have hmem : g⁻¹ * k * g ∈ Subgroup.centralizer (M.D.rootGroup β : Set M.K) :=
    hC (g⁻¹ * x * g) hxg hxg1 hkg
  rw [Subgroup.mem_centralizer_iff] at hmem
  have hyg : g⁻¹ * y * g ∈ M.D.rootGroup β := by
    have hy' := hy
    rw [← hg] at hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    have hzy' : g * z * g⁻¹ = y := by simpa [MulAut.conj_apply] using hzy
    have hz_eq : z = g⁻¹ * y * g := by rw [← hzy']; group
    rwa [hz_eq] at hz
  have hcomm := hmem (g⁻¹ * y * g) hyg
  calc y * k = g * ((g⁻¹ * y * g) * (g⁻¹ * k * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * k * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm]
    _ = k * y := by group

private theorem rckJB8910_sq_surjective_fixedUnits {F : Type} [Field F] [CharP F 2] [Finite F]
    (σ : F →+* F) : Function.Surjective (fun t : fixedUnits σ => t * t) := by
  haveI : Finite (fixedUnits σ) := inferInstance
  have hsq : ∀ x : Fˣ, x * x = 1 → x = 1 := by
    intro x hx
    have hx' : (x : F) * (x : F) = 1 := by
      simpa using congrArg (fun u : Fˣ => (u : F)) hx
    rcases (mul_self_eq_one_iff (a := (x : F))).1 hx' with h | h
    · exact Units.ext h
    · refine Units.ext ?_
      rw [h]
      exact CharTwo.neg_eq 1
  have hinj : Function.Injective (fun t : fixedUnits σ => t * t) := by
    intro s t hst
    apply Subtype.ext
    have hst' : (s : Fˣ) * (s : Fˣ) = (t : Fˣ) * (t : Fˣ) := by
      simpa only [Subgroup.coe_mul] using congrArg Subtype.val hst
    have h1 : ((s : Fˣ) * (t : Fˣ)⁻¹) * ((s : Fˣ) * (t : Fˣ)⁻¹) = 1 := by
      calc ((s : Fˣ) * (t : Fˣ)⁻¹) * ((s : Fˣ) * (t : Fˣ)⁻¹)
            = ((s : Fˣ) * (s : Fˣ)) * ((t : Fˣ)⁻¹ * (t : Fˣ)⁻¹) := by ac_rfl
        _ = ((t : Fˣ) * (t : Fˣ)) * ((t : Fˣ)⁻¹ * (t : Fˣ)⁻¹) := by rw [hst']
        _ = 1 := by rw [← mul_inv_rev, mul_inv_cancel]
    have h2 : (s : Fˣ) * (t : Fˣ)⁻¹ = 1 := hsq _ h1
    rwa [mul_inv_eq_one] at h2
  exact Finite.surjective_of_injective hinj

private theorem rckJB8910_trans_betaZero
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hF : TriField F σ g) :
    ∀ x ∈ twistedRootGroup σ (Pi.single (ng 0) 1), x ≠ 1 →
      ∀ y ∈ twistedRootGroup σ (Pi.single (ng 0) 1), y ≠ 1 →
        ∃ n ∈ Subgroup.normalizer
            (twistedRootGroup σ (Pi.single (ng 0) 1) : Set (twistedGroup σ)),
          n * x * n⁻¹ = y := by
  have hσ : ∀ c, σ (σ (σ c)) = c := sigma_three_of_card hF.2.1 hF.2.2
  haveI hchar : CharP F 2 := charP_two_of_triField hF
  have hsurj := rckJB8910_sq_surjective_fixedUnits (F := F) σ
  intro x hx hx1 y hy hy1
  obtain ⟨c, hc, hxc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ
    (isRoot_single d4 (nd 2)) proj_single_two rho_single_two (x : adjointGroup d4 F)).1
    ((mem_twistedRootGroup (σ := σ)).1 hx)
  obtain ⟨d, hd, hyd⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ
    (isRoot_single d4 (nd 2)) proj_single_two rho_single_two (y : adjointGroup d4 F)).1
    ((mem_twistedRootGroup (σ := σ)).1 hy)
  have hc0 : c ≠ 0 := by
    intro h
    apply hx1
    apply Subtype.ext
    rw [hxc, h, xPar_zero]
    rfl
  have hd0 : d ≠ 0 := by
    intro h
    apply hy1
    apply Subtype.ext
    rw [hyd, h, xPar_zero]
    rfl
  have hcu : Units.mk0 c hc0 ∈ fixedUnits σ := by
    rw [mem_fixedUnits]; simpa using hc
  have hdu : Units.mk0 d hd0 ∈ fixedUnits σ := by
    rw [mem_fixedUnits]; simpa using hd
  let cu : fixedUnits σ := ⟨Units.mk0 c hc0, hcu⟩
  let du : fixedUnits σ := ⟨Units.mk0 d hd0, hdu⟩
  obtain ⟨t, ht⟩ := hsurj (du * cu⁻¹)
  have ht' : ((t : Fˣ) : F) * ((t : Fˣ) : F) * c = d := by
    have h := congrArg (fun u : fixedUnits σ => ((u : Fˣ) : F) * c) ht
    have h2 : ((t : Fˣ) : F) * ((t : Fˣ) : F) * c = d * c⁻¹ * c := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_inv_eq_inv_val,
        cu, du, Units.val_mk0] using h
    have hdc : d * c⁻¹ * c = d := by rw [mul_assoc, inv_mul_cancel₀ hc0, mul_one]
    rwa [hdc] at h2
  have ht'' : (↑((t : Fˣ) ^ 2) : F) * c = d := by
    simp only [pow_two, Units.val_mul]
    exact ht'
  have htfix : σ ((t : Fˣ) : F) = ((t : Fˣ) : F) := (mem_fixedUnits σ).1 t.2
  obtain ⟨n, hn_mem, hn_val⟩ := exists_hLongElt (σ := σ) htfix
  refine ⟨n, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact hHat_conj_mem (σ := σ) (ng 0) (IsRoot.basis (ng 0)) hn_mem hz
    · intro hz
      have h1 := hHat_conj_mem (σ := σ) (ng 0) (IsRoot.basis (ng 0)) (inv_mem hn_mem) hz
      have hz_eq : n⁻¹ * (n * z * n⁻¹) * (n⁻¹)⁻¹ = z := by group
      rwa [hz_eq] at h1
  · apply Subtype.ext
    have hxadj : (x : adjointGroup d4 F) =
        xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) c := hxc
    have hyadj : (y : adjointGroup d4 F) =
        xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) d := hyd
    change (n : adjointGroup d4 F) * (x : adjointGroup d4 F) *
        (n : adjointGroup d4 F)⁻¹ = (y : adjointGroup d4 F)
    rw [hxadj, hyadj, hn_val]
    rw [xPar_of_isRoot (isRoot_single d4 (nd 2)) c,
      xPar_of_isRoot (isRoot_single d4 (nd 2)) d]
    rw [(rootOperatorFamily d4).torusElement_mul_eltElement_mul_inv (nd 2) (t : Fˣ)
      ⟨Pi.single (nd 2) 1, isRoot_single d4 (nd 2)⟩ c]
    rw [show (∑ j, d4.cartan (nd 2) j *
        (Pi.single (nd 2) 1 : Fin d4.rank → ℤ) j) = 2 by decide +kernel]
    exact congrArg ((rootOperatorFamily d4).eltElement
      ⟨Pi.single (nd 2) 1, isRoot_single d4 (nd 2)⟩) ht''

private theorem rckJB8910_trans_conj {M : LieUniversal} {β β' : Fin M.D.rank → ℤ} {g : M.K}
    (hg : (M.D.rootGroup β).map (MulAut.conj g).toMonoidHom = M.D.rootGroup β')
    (htr : ∀ x ∈ M.D.rootGroup β, x ≠ 1 → ∀ y ∈ M.D.rootGroup β, y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (M.D.rootGroup β : Set M.K), n * x * n⁻¹ = y) :
    ∀ x ∈ M.D.rootGroup β', x ≠ 1 → ∀ y ∈ M.D.rootGroup β', y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (M.D.rootGroup β' : Set M.K), n * x * n⁻¹ = y := by
  intro x hx hx1 y hy hy1
  have hxg : g⁻¹ * x * g ∈ M.D.rootGroup β := by
    have hx' := hx
    rw [← hg] at hx'
    obtain ⟨w, hw, hwx⟩ := hx'
    have hwx' : g * w * g⁻¹ = x := by simpa [MulAut.conj_apply] using hwx
    have : w = g⁻¹ * x * g := by rw [← hwx']; group
    rwa [this] at hw
  have hyg : g⁻¹ * y * g ∈ M.D.rootGroup β := by
    have hy' := hy
    rw [← hg] at hy'
    obtain ⟨w, hw, hwy⟩ := hy'
    have hwy' : g * w * g⁻¹ = y := by simpa [MulAut.conj_apply] using hwy
    have : w = g⁻¹ * y * g := by rw [← hwy']; group
    rwa [this] at hw
  have hxg1 : g⁻¹ * x * g ≠ 1 := by
    intro h
    apply hx1
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [h]
      _ = 1 := by group
  have hyg1 : g⁻¹ * y * g ≠ 1 := by
    intro h
    apply hy1
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [h]
      _ = 1 := by group
  obtain ⟨n, hn, hnxy⟩ := htr (g⁻¹ * x * g) hxg hxg1 (g⁻¹ * y * g) hyg hyg1
  refine ⟨g * n * g⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro z
    constructor
    · intro hz
      have hzg : g⁻¹ * z * g ∈ M.D.rootGroup β := by
        have hz' := hz
        rw [← hg] at hz'
        obtain ⟨w, hw, hwz⟩ := hz'
        have hwz' : g * w * g⁻¹ = z := by simpa [MulAut.conj_apply] using hwz
        have : w = g⁻¹ * z * g := by rw [← hwz']; group
        rwa [this] at hw
      rw [← hg]
      exact ⟨n * (g⁻¹ * z * g) * n⁻¹, (hn _).1 hzg, by
        change g * (n * (g⁻¹ * z * g) * n⁻¹) * g⁻¹ =
          (g * n * g⁻¹) * z * (g * n * g⁻¹)⁻¹
        group⟩
    · intro hz
      have hzβ : n * (g⁻¹ * z * g) * n⁻¹ ∈ M.D.rootGroup β := by
        have hz' := hz
        rw [← hg] at hz'
        obtain ⟨w, hw, hwz⟩ := hz'
        have hwz' : g * w * g⁻¹ = (g * n * g⁻¹) * z * (g * n * g⁻¹)⁻¹ := by
          simpa [MulAut.conj_apply] using hwz
        have : w = n * (g⁻¹ * z * g) * n⁻¹ := by
          calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
            _ = g⁻¹ * ((g * n * g⁻¹) * z * (g * n * g⁻¹)⁻¹) * g := by rw [hwz']
            _ = n * (g⁻¹ * z * g) * n⁻¹ := by group
        rwa [this] at hw
      have hzg : g⁻¹ * z * g ∈ M.D.rootGroup β := (hn (g⁻¹ * z * g)).2 hzβ
      rw [← hg]
      exact ⟨g⁻¹ * z * g, hzg, by
        change g * (g⁻¹ * z * g) * g⁻¹ = z
        group⟩
  · calc (g * n * g⁻¹) * x * (g * n * g⁻¹)⁻¹ =
        g * (n * (g⁻¹ * x * g) * n⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g) * g⁻¹ := by rw [hnxy]
      _ = y := by group

theorem rckHB_cent_triD4
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hF : TriField F σ g)
    {β : Fin (triD4Universal F σ).D.rank → ℤ} (hβ : GGLongRoot (triD4Universal F σ).D β) :
    RCKLemmaHCent (triD4Universal F σ) β := by
  show RCKLemmaHCent ⟨↥(twistedGroup σ), twistedDatum σ⟩ β
  haveI hchar : CharP F 2 := charP_two_of_triField hF
  have hσ : ∀ c, σ (σ (σ c)) = c := sigma_three_of_card hF.2.1 hF.2.2
  have hC0 : RCKLemmaHCent ⟨↥(twistedGroup σ), twistedDatum σ⟩ (Pi.single (ng 0) 1) := by
    intro x hx hx1 k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxsub : (x : adjointGroup d4 F) ∈ twistedRootSubgroupD4 σ (Pi.single (ng 0) 1) :=
      (mem_twistedRootGroup (σ := σ)).1 hx
    have hysub : (y : adjointGroup d4 F) ∈ twistedRootSubgroupD4 σ (Pi.single (ng 0) 1) :=
      (mem_twistedRootGroup (σ := σ)).1 hy
    have hxrg : (x : adjointGroup d4 F) ∈
        rootGroup (rootOperatorFamily d4) F (Pi.single (nd 2) 1) := by
      obtain ⟨c, _, hxc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_single d4 (nd 2))
        proj_single_two rho_single_two _).1 hxsub
      rw [hxc]
      exact xPar_mem (isRoot_single d4 (nd 2)) c
    have hyrg : (y : adjointGroup d4 F) ∈
        rootGroup (rootOperatorFamily d4) F (Pi.single (nd 2) 1) := by
      obtain ⟨c, _, hyc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_single d4 (nd 2))
        proj_single_two rho_single_two _).1 hysub
      rw [hyc]
      exact xPar_mem (isRoot_single d4 (nd 2)) c
    have hxrg1 : (x : adjointGroup d4 F) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hk' : (k : adjointGroup d4 F) ∈
        (Subgroup.centralizer {(x : adjointGroup d4 F)} : Subgroup (adjointGroup d4 F)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      simpa only [Subgroup.coe_mul] using
        congrArg (fun z : twistedGroup σ => (z : adjointGroup d4 F))
          (Subgroup.mem_centralizer_singleton_iff.1 hk)
    have hmem := rckJB8910_cent_D4_rootGroup (isRoot_single d4 (nd 2)) hxrg hxrg1 hk'
    rw [Subgroup.mem_centralizer_iff] at hmem
    show y * k = k * y
    exact Subtype.ext (by
      simpa only [Subgroup.coe_mul] using hmem (y : adjointGroup d4 F) hyrg)
  let β' : Fin (Tag.rank .G2) → ℤ := β
  have hβ' : GGLongRoot (twistedDatum σ) β' := hβ
  obtain ⟨w, hw⟩ := rckJB8910_long_orbit hF hβ'
  have hct := twistedDatum_isCTGroupDatum σ hσ
  obtain ⟨g', hg'⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_map_conj_rootGroup hct w⁻¹
  have hw' : w⁻¹ • (Pi.single (ng 0) 1) = β' := by rw [← hw, inv_smul_smul]
  have hw'' : (weylAction (twistedDatum σ).isFiniteType w⁻¹ (Pi.single (ng 0) 1)) = β' := hw'
  have hgβ : ((twistedDatum σ).rootGroup (Pi.single (ng 0) 1)).map
      (MulAut.conj g').toMonoidHom = (twistedDatum σ).rootGroup β' := by
    have h := hg' (Pi.single (ng 0) 1) (by rw [twistedDatum_roots]; exact IsRoot.basis (ng 0))
    rwa [hw''] at h
  exact rckJB8910_cent_conj hgβ hC0

theorem rckHB_transitive_triD4
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hF : TriField F σ g)
    {β : Fin (triD4Universal F σ).D.rank → ℤ} (hβ : GGLongRoot (triD4Universal F σ).D β) :
    ∀ x ∈ (triD4Universal F σ).D.rootGroup β, x ≠ 1 → ∀ y ∈ (triD4Universal F σ).D.rootGroup β, y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer ((triD4Universal F σ).D.rootGroup β : Set (triD4Universal F σ).K),
        n * x * n⁻¹ = y := by
  let β' : Fin (Tag.rank .G2) → ℤ := β
  show ∀ x ∈ twistedRootGroup σ β', x ≠ 1 →
      ∀ y ∈ twistedRootGroup σ β', y ≠ 1 →
        ∃ n ∈ Subgroup.normalizer (twistedRootGroup σ β' : Set (twistedGroup σ)), n * x * n⁻¹ = y
  have hσ : ∀ c, σ (σ (σ c)) = c := sigma_three_of_card hF.2.1 hF.2.2
  have htr0 := rckJB8910_trans_betaZero hF
  have hβ' : GGLongRoot (twistedDatum σ) β' := hβ
  obtain ⟨w, hw⟩ := rckJB8910_long_orbit hF hβ'
  have hct := twistedDatum_isCTGroupDatum σ hσ
  obtain ⟨gp, hgp⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_map_conj_rootGroup hct w⁻¹
  have hw' : w⁻¹ • (Pi.single (ng 0) 1) = β' := by rw [← hw, inv_smul_smul]
  have hw'' : (weylAction (twistedDatum σ).isFiniteType w⁻¹ (Pi.single (ng 0) 1)) = β' := hw'
  have hgβ : (twistedRootGroup σ (Pi.single (ng 0) 1)).map
      (MulAut.conj gp).toMonoidHom = twistedRootGroup σ β' := by
    have h := hgp (Pi.single (ng 0) 1)
      (by rw [twistedDatum_roots]; exact IsRoot.basis (ng 0))
    rwa [hw''] at h
  exact rckJB8910_trans_conj (M := ⟨↥(twistedGroup σ), twistedDatum σ⟩)
    (β := Pi.single (ng 0) 1) (β' := β') (g := gp) hgβ htr0

theorem rck_lemmaH_triD4
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hF : TriField F σ g)
    {β : Fin (triD4Universal F σ).D.rank → ℤ} (hβ : GGLongRoot (triD4Universal F σ).D β) :
    RCKLemmaHTI (triD4Universal F σ) β ∧ RCKLemmaHLevi (triD4Universal F σ) β := by
  have hC := rckHB_cent_triD4 hF hβ
  exact ⟨rckHB_TI_of_cent hC (rckHB_transitive_triD4 hF hβ), rckHB_levi_of_cent hC⟩

end CFSG.StandardType.RCKC1
